import NetHack.Soko22Hazard87.AndIntroBlocks0306
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro76750 (p : Pattern) (ha : d288492 p = 1) (hb : d297931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288273 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288375 q = 1) (hb : d296617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288375, d296617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76746 q ha hb
    | true =>
      simp only [d288375, d296617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76747 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288388 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288389 q = 1) (hb : d296618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288389, d296618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288389, d296618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288390 q = 1) (hb : d297912 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288390, d297912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288390, d297912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288391 q = 1) (hb : d297913 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288391, d297913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288391, d297913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288395 q = 1) (hb : d297915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288395, d297915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288395, d297915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76748 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d288397 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d288398 q = 1) (hb : d297916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288398, d297916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288398, d297916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288399 q = 1) (hb : d297917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288399, d297917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288399, d297917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d288400 q = 1) (hb : d297918 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288400, d297918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288400, d297918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d288401 q = 1) (hb : d297919 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288401, d297919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288401, d297919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288480 q = 1) (hb : d297926 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288480, d297926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288480, d297926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76749 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288488 q = 1) (hb : d297927 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288488, d297927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288488, d297927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288489 q = 1) (hb : d297928 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288489, d297928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288489, d297928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d288490 q = 1) (hb : d297929 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288490, d297929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288490, d297929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d288491 q = 1) (hb : d297930 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288491, d297930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288491, d297930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d288492 q = 1) (hb : d297931 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288492, d297931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288492, d297931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76751 (p : Pattern) (ha : d288498 p = 1) (hb : d297937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288493 q = 1) (hb : d297932 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288493, d297932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288493, d297932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76750 q ha hb
  have h2 (q : Pattern) (ha : d288494 q = 1) (hb : d297933 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288494, d297933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288494, d297933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288495 q = 1) (hb : d297934 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288495, d297934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288495, d297934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288496 q = 1) (hb : d297935 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288496, d297935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288496, d297935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288497 q = 1) (hb : d297936 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288497, d297936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288497, d297936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288498 q = 1) (hb : d297937 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288498, d297937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288498, d297937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76752 (p : Pattern) (ha : d288672 p = 1) (hb : d296900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288600 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288609 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d288652 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d288574 q = 1) (hb : d296895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d296895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76571 q ha hb
    | true =>
      simp only [d288574, d296895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76572 q ha hb
  have h5 (q : Pattern) (ha : d288653 q = 1) (hb : d296896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d288653, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d288668 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d288669 q = 1) (hb : d296897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288669, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d288670 q = 1) (hb : d296898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d288670, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d288671 q = 1) (hb : d296899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288671, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288672 q = 1) (hb : d296900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288672, d296900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288672, d296900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76753 (p : Pattern) (ha : d288693 p = 1) (hb : d296910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288574 q = 1) (hb : d296895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288574, d296895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76571 q ha hb
    | true =>
      simp only [d288574, d296895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76572 q ha hb
  have h4 (q : Pattern) (ha : d288653 q = 1) (hb : d296896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288653, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d288653, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d288668 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d288669 q = 1) (hb : d296897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288669, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d288669, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d288670 q = 1) (hb : d296898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288670, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288670, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288671 q = 1) (hb : d296899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288671, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288671, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d288678 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d288683 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d288685 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d288584 q = 1) (hb : d296905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288584, d296905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76574 q ha hb
    | true =>
      simp only [d288584, d296905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76575 q ha hb
  have h13 (q : Pattern) (ha : d288686 q = 1) (hb : d296906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d288686, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288689 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288690 q = 1) (hb : d296907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288690, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288691 q = 1) (hb : d296908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288691, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d288691, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d288692 q = 1) (hb : d296909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288692, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d288692, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d288693 q = 1) (hb : d296910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288693, d296910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288693, d296910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76754 (p : Pattern) (ha : d288713 p = 1) (hb : d297942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288584 q = 1) (hb : d296905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288584, d296905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76574 q ha hb
    | true =>
      simp only [d288584, d296905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76575 q ha hb
  have h3 (q : Pattern) (ha : d288686 q = 1) (hb : d296906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288686, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288686, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288689 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288690 q = 1) (hb : d296907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288690, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288690, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288711 q = 1) (hb : d296908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288711, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288711, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288712 q = 1) (hb : d296909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288712, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288712, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288713 q = 1) (hb : d297942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288713, d297942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288713, d297942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76755 (p : Pattern) (ha : d288825 p = 1) (hb : d297953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288805 q = 1) (hb : d297948 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288805, d297948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76612 q ha hb
    | true =>
      simp only [d288805, d297948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76617 q ha hb
  have h3 (q : Pattern) (ha : d288806 q = 1) (hb : d297949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d288806, d297949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288806, d297949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d288821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288822 q = 1) (hb : d297950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288822, d297950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288822, d297950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288823 q = 1) (hb : d297951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d288823, d297951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288823, d297951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288824 q = 1) (hb : d297952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d288824, d297952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288824, d297952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288825 q = 1) (hb : d297953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d288825, d297953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288825, d297953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76756 (p : Pattern) (ha : d288838 p = 1) (hb : d297959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288694 q = 1) (hb : d296911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288694, d296911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76752 q ha hb
    | true =>
      simp only [d288694, d296911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76753 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288708 q = 1) (hb : d296912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288708, d296912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d288708, d296912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288709 q = 1) (hb : d297940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288709, d297940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288709, d297940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d288710 q = 1) (hb : d297941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288710, d297941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288710, d297941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d288714 q = 1) (hb : d297943 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288714, d297943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288714, d297943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76754 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d288716 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d288717 q = 1) (hb : d297944 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288717, d297944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288717, d297944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288718 q = 1) (hb : d297945 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288718, d297945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288718, d297945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d288719 q = 1) (hb : d297946 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288719, d297946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d288719, d297946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d288720 q = 1) (hb : d297947 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288720, d297947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d288720, d297947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288826 q = 1) (hb : d297954 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d288826, d297954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d288826, d297954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76755 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d288833 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d288834 q = 1) (hb : d297955 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d288834, d297955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d288834, d297955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d288835 q = 1) (hb : d297956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d288835, d297956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d288835, d297956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d288836 q = 1) (hb : d297957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d288836, d297957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d288836, d297957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d288837 q = 1) (hb : d297958 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d288837, d297958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d288837, d297958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d288838 q = 1) (hb : d297959 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d288838, d297959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288838, d297959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76757 (p : Pattern) (ha : d288844 p = 1) (hb : d297965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d288839 q = 1) (hb : d297960 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d288839, d297960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288839, d297960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76756 q ha hb
  have h2 (q : Pattern) (ha : d288840 q = 1) (hb : d297961 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d288840, d297961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288840, d297961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288841 q = 1) (hb : d297962 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d288841, d297962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288841, d297962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288842 q = 1) (hb : d297963 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d288842, d297963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288842, d297963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d288843 q = 1) (hb : d297964 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d288843, d297964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288843, d297964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288844 q = 1) (hb : d297965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d288844, d297965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d288844, d297965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76758 (p : Pattern) (ha : d289046 p = 1) (hb : d297245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d288983 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d289013 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d288948 q = 1) (hb : d297240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d297240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76635 q ha hb
    | true =>
      simp only [d288948, d297240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76636 q ha hb
  have h5 (q : Pattern) (ha : d289014 q = 1) (hb : d297241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289014, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d289042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289043 q = 1) (hb : d297242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289043, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d289044 q = 1) (hb : d297243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289044, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289045 q = 1) (hb : d297244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289045, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289046 q = 1) (hb : d297245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289046, d297245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289046, d297245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76759 (p : Pattern) (ha : d289067 p = 1) (hb : d297255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d288983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d288948 q = 1) (hb : d297240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288948, d297240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76635 q ha hb
    | true =>
      simp only [d288948, d297240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76636 q ha hb
  have h4 (q : Pattern) (ha : d289014 q = 1) (hb : d297241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289014, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289014, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d289042 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289043 q = 1) (hb : d297242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289043, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289043, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d289044 q = 1) (hb : d297243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289044, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289044, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289045 q = 1) (hb : d297244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289045, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289045, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d289052 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d289057 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d289059 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d288958 q = 1) (hb : d297250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288958, d297250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76638 q ha hb
    | true =>
      simp only [d288958, d297250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76639 q ha hb
  have h13 (q : Pattern) (ha : d289060 q = 1) (hb : d297251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289060, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d289063 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289064 q = 1) (hb : d297252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289064, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289065 q = 1) (hb : d297253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289065, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289065, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289066 q = 1) (hb : d297254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289066, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289066, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289067 q = 1) (hb : d297255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289067, d297255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289067, d297255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76760 (p : Pattern) (ha : d289087 p = 1) (hb : d297971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d289059 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288958 q = 1) (hb : d297250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d288958, d297250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76638 q ha hb
    | true =>
      simp only [d288958, d297250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76639 q ha hb
  have h3 (q : Pattern) (ha : d289060 q = 1) (hb : d297251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289060, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289060, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289063 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289064 q = 1) (hb : d297252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289064, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289064, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289085 q = 1) (hb : d297253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289085, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289085, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289086 q = 1) (hb : d297254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289086, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289086, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289087 q = 1) (hb : d297971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289087, d297971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289087, d297971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76761 (p : Pattern) (ha : d289210 p = 1) (hb : d297982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d289174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d289179 q = 1) (hb : d297977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d289179, d297977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76678 q ha hb
    | true =>
      simp only [d289179, d297977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76684 q ha hb
  have h3 (q : Pattern) (ha : d289180 q = 1) (hb : d297978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289180, d297978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289180, d297978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d289206 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289207 q = 1) (hb : d297979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289207, d297979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289207, d297979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289208 q = 1) (hb : d297980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289208, d297980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289208, d297980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289209 q = 1) (hb : d297981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289209, d297981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289209, d297981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289210 q = 1) (hb : d297982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289210, d297982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289210, d297982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76762 (p : Pattern) (ha : d289223 p = 1) (hb : d297988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d288966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289068 q = 1) (hb : d297256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289068, d297256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76758 q ha hb
    | true =>
      simp only [d289068, d297256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d289081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289082 q = 1) (hb : d297257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289082, d297257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289082, d297257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289083 q = 1) (hb : d297969 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289083, d297969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289083, d297969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289084 q = 1) (hb : d297970 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289084, d297970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289084, d297970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289088 q = 1) (hb : d297972 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289088, d297972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289088, d297972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76760 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d289090 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289091 q = 1) (hb : d297973 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289091, d297973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289091, d297973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289092 q = 1) (hb : d297974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289092, d297974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289092, d297974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d289093 q = 1) (hb : d297975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289093, d297975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289093, d297975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d289094 q = 1) (hb : d297976 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289094, d297976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289094, d297976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289211 q = 1) (hb : d297983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289211, d297983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d289211, d297983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76761 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d289218 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289219 q = 1) (hb : d297984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289219, d297984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289219, d297984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289220 q = 1) (hb : d297985 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289220, d297985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289220, d297985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d289221 q = 1) (hb : d297986 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289221, d297986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289221, d297986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d289222 q = 1) (hb : d297987 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289222, d297987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289222, d297987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d289223 q = 1) (hb : d297988 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289223, d297988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289223, d297988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76763 (p : Pattern) (ha : d289229 p = 1) (hb : d297994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289224 q = 1) (hb : d297989 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289224, d297989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289224, d297989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76762 q ha hb
  have h2 (q : Pattern) (ha : d289225 q = 1) (hb : d297990 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289225, d297990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289225, d297990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289226 q = 1) (hb : d297991 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289226, d297991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289226, d297991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289227 q = 1) (hb : d297992 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289227, d297992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289227, d297992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289228 q = 1) (hb : d297993 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289228, d297993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289228, d297993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289229 q = 1) (hb : d297994 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289229, d297994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289229, d297994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76764 (p : Pattern) (ha : d289235 p = 1) (hb : d298030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d288219 q = 1) (hb : d297911 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288219, d297911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76739 q ha hb
    | true =>
      simp only [d288219, d297911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76745 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d288499 q = 1) (hb : d297938 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288499, d297938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288499, d297938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76751 q ha hb
  have h3 (q : Pattern) (ha : d288500 q = 1) (hb : d297939 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288500, d297939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d288500, d297939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288845 q = 1) (hb : d297966 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d288845, d297966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288845, d297966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76757 q ha hb
  have h5 (q : Pattern) (ha : d288846 q = 1) (hb : d297967 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d288846, d297967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d288846, d297967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288847 q = 1) (hb : d297968 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d288847, d297968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288847, d297968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289230 q = 1) (hb : d297995 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289230, d297995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289230, d297995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76763 q ha hb
  have h8 (q : Pattern) (ha : d289231 q = 1) (hb : d297996 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d289231, d297996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289231, d297996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289232 q = 1) (hb : d297997 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d289232, d297997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289232, d297997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289233 q = 1) (hb : d297998 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d289233, d297998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289233, d297998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d280886 q = 1) (hb : d298025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d280886, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d280886, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76733 q ha hb
  have h12 (q : Pattern) (ha : d280887 q = 1) (hb : d298026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d280887, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d280887, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d280888 q = 1) (hb : d298027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d280888, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d280888, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d280889 q = 1) (hb : d298028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d280889, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d280889, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d289234 q = 1) (hb : d298029 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d289234, d298029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289234, d298029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d289235 q = 1) (hb : d298030 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d289235, d298030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289235, d298030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro76765 (p : Pattern) (ha : d289241 p = 1) (hb : d298036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289236 q = 1) (hb : d298031 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d289236, d298031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76764 q ha hb
    | true =>
      simp only [d289236, d298031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289237 q = 1) (hb : d298032 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d289237, d298032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289237, d298032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289238 q = 1) (hb : d298033 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d289238, d298033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289238, d298033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289239 q = 1) (hb : d298034 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d289239, d298034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289239, d298034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289240 q = 1) (hb : d298035 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d289240, d298035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289240, d298035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289241 q = 1) (hb : d298036 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d289241, d298036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289241, d298036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76766 (p : Pattern) (ha : d289247 p = 1) (hb : d298042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289242 q = 1) (hb : d298037 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d289242, d298037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76765 q ha hb
    | true =>
      simp only [d289242, d298037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289243 q = 1) (hb : d298038 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d289243, d298038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289243, d298038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289244 q = 1) (hb : d298039 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d289244, d298039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289244, d298039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289245 q = 1) (hb : d298040 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d289245, d298040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289245, d298040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289246 q = 1) (hb : d298041 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d289246, d298041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289246, d298041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289247 q = 1) (hb : d298042 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d289247, d298042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289247, d298042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76767 (p : Pattern) (ha : d289253 p = 1) (hb : d298048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289248 q = 1) (hb : d298043 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d289248, d298043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76766 q ha hb
    | true =>
      simp only [d289248, d298043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289249 q = 1) (hb : d298044 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d289249, d298044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289249, d298044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289250 q = 1) (hb : d298045 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d289250, d298045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289250, d298045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289251 q = 1) (hb : d298046 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d289251, d298046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289251, d298046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289252 q = 1) (hb : d298047 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d289252, d298047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289252, d298047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289253 q = 1) (hb : d298048 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d289253, d298048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289253, d298048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76768 (p : Pattern) (ha : d289259 p = 1) (hb : d298054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289254 q = 1) (hb : d298049 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d289254, d298049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76767 q ha hb
    | true =>
      simp only [d289254, d298049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289255 q = 1) (hb : d298050 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d289255, d298050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289255, d298050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289256 q = 1) (hb : d298051 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d289256, d298051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289256, d298051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289257 q = 1) (hb : d298052 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d289257, d298052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289257, d298052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289258 q = 1) (hb : d298053 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d289258, d298053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289258, d298053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289259 q = 1) (hb : d298054 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d289259, d298054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289259, d298054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76769 (p : Pattern) (ha : d289265 p = 1) (hb : d298060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289260 q = 1) (hb : d298055 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d289260, d298055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76768 q ha hb
    | true =>
      simp only [d289260, d298055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289261 q = 1) (hb : d298056 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d289261, d298056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289261, d298056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289262 q = 1) (hb : d298057 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d289262, d298057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289262, d298057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289263 q = 1) (hb : d298058 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d289263, d298058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289263, d298058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289264 q = 1) (hb : d298059 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d289264, d298059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289264, d298059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289265 q = 1) (hb : d298060 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d289265, d298060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289265, d298060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76770 (p : Pattern) (ha : d289271 p = 1) (hb : d298066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289266 q = 1) (hb : d298061 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d289266, d298061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76769 q ha hb
    | true =>
      simp only [d289266, d298061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289267 q = 1) (hb : d298062 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d289267, d298062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289267, d298062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289268 q = 1) (hb : d298063 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d289268, d298063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289268, d298063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289269 q = 1) (hb : d298064 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d289269, d298064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289269, d298064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289270 q = 1) (hb : d298065 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d289270, d298065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289270, d298065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289271 q = 1) (hb : d298066 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d289271, d298066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289271, d298066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76771 (p : Pattern) (ha : d289277 p = 1) (hb : d298072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289272 q = 1) (hb : d298067 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d289272, d298067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76770 q ha hb
    | true =>
      simp only [d289272, d298067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d289273 q = 1) (hb : d298068 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d289273, d298068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289273, d298068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d289274 q = 1) (hb : d298069 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d289274, d298069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d289274, d298069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d289275 q = 1) (hb : d298070 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d289275, d298070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289275, d298070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d289276 q = 1) (hb : d298071 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d289276, d298071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289276, d298071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d289277 q = 1) (hb : d298072 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d289277, d298072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289277, d298072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro76772 (p : Pattern) (ha : d281023 p = 1) (hb : d297570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d39781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d39790 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d39807 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281019 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d281019, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d39891 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d281020 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281020, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d281021 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d281021, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d281022 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281022, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d281023 q = 1) (hb : d297570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281023, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281023, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76773 (p : Pattern) (ha : d281028 p = 1) (hb : d297580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d39781 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d39790 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d39807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d297565 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d281019 q = 1) (hb : d297566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281019, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d281019, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d39891 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281020 q = 1) (hb : d297567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281020, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281020, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d281021 q = 1) (hb : d297568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281021, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281021, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d281022 q = 1) (hb : d297569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281022, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281022, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d39901 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d39906 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d39908 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d281024 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d281024, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d39915 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d281025 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d281025, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d281026 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281026, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d281026, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d281027 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281027, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d281027, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d281028 q = 1) (hb : d297580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281028, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d281028, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76774 (p : Pattern) (ha : d281035 p = 1) (hb : d298001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d39908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281024 q = 1) (hb : d297576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281024, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281024, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d39915 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281025 q = 1) (hb : d297577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281025, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281025, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d281033 q = 1) (hb : d297578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281033, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281033, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d281034 q = 1) (hb : d297579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281034, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281034, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d281035 q = 1) (hb : d298001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281035, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281035, d298001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76775 (p : Pattern) (ha : d281045 p = 1) (hb : d298012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40002 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281041 q = 1) (hb : d298008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d281041, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d281041, d298008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281042 q = 1) (hb : d298009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281042, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281042, d298009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d281043 q = 1) (hb : d298010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d281043, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281043, d298010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d281044 q = 1) (hb : d298011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d281044, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281044, d298011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d281045 q = 1) (hb : d298012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d281045, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281045, d298012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76776 (p : Pattern) (ha : d281051 p = 1) (hb : d298018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d39773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d281029 q = 1) (hb : d297581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281029, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76772 q ha hb
    | true =>
      simp only [d281029, d297581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76773 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d39933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d281030 q = 1) (hb : d297582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281030, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281030, d297582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281031 q = 1) (hb : d297999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281031, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281031, d297999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281032 q = 1) (hb : d298000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281032, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d281032, d298000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d281036 q = 1) (hb : d298002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281036, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281036, d298002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76774 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d39942 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d281037 q = 1) (hb : d298003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281037, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d281037, d298003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d281038 q = 1) (hb : d298004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281038, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d281038, d298004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d281039 q = 1) (hb : d298005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281039, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d281039, d298005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d281040 q = 1) (hb : d298006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281040, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d281040, d298006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d281046 q = 1) (hb : d298013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d281046, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281046, d298013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76775 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40089 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d281047 q = 1) (hb : d298014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d281047, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d281047, d298014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d281048 q = 1) (hb : d298015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d281048, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d281048, d298015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d281049 q = 1) (hb : d298016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d281049, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d281049, d298016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d281050 q = 1) (hb : d298017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d281050, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d281050, d298017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d281051 q = 1) (hb : d298018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d281051, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d281051, d298018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76777 (p : Pattern) (ha : d281057 p = 1) (hb : d298024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d281052 q = 1) (hb : d298019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d281052, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281052, d298019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76776 q ha hb
  have h2 (q : Pattern) (ha : d281053 q = 1) (hb : d298020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d281053, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281053, d298020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281054 q = 1) (hb : d298021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d281054, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281054, d298021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281055 q = 1) (hb : d298022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d281055, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281055, d298022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d281056 q = 1) (hb : d298023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d281056, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281056, d298023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281057 q = 1) (hb : d298024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d281057, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d281057, d298024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76778 (p : Pattern) (ha : d289320 p = 1) (hb : d296179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d296115 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289316 q = 1) (hb : d296175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289316, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40332 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289317 q = 1) (hb : d296176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289317, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d289318 q = 1) (hb : d296177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289318, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289319 q = 1) (hb : d296178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289319, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289320 q = 1) (hb : d296179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289320, d296179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289320, d296179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76779 (p : Pattern) (ha : d289325 p = 1) (hb : d296186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40256 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40262 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d296115 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d289316 q = 1) (hb : d296175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289316, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289316, d296175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40332 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289317 q = 1) (hb : d296176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289317, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289317, d296176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d289318 q = 1) (hb : d296177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289318, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289318, d296177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289319 q = 1) (hb : d296178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289319, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289319, d296178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40341 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40345 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40347 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d296122 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d289321 q = 1) (hb : d296182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289321, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40353 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289322 q = 1) (hb : d296183 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289322, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289323 q = 1) (hb : d296184 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289323, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289323, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289324 q = 1) (hb : d296185 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289324, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289324, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289325 q = 1) (hb : d296186 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289325, d296186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289325, d296186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76780 (p : Pattern) (ha : d289332 p = 1) (hb : d297862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d296122 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289321 q = 1) (hb : d296182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289321, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289321, d296182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40353 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289322 q = 1) (hb : d296183 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289322, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289322, d296183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289330 q = 1) (hb : d296184 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289330, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289330, d296184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289331 q = 1) (hb : d296185 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289331, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289331, d296185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289332 q = 1) (hb : d297862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289332, d297862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289332, d297862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76781 (p : Pattern) (ha : d289342 p = 1) (hb : d297872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d296158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289338 q = 1) (hb : d297868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289338, d297868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289338, d297868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40421 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289339 q = 1) (hb : d297869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289339, d297869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289339, d297869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289340 q = 1) (hb : d297870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289340, d297870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289340, d297870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289341 q = 1) (hb : d297871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289341, d297871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289341, d297871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289342 q = 1) (hb : d297872 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289342, d297872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289342, d297872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76782 (p : Pattern) (ha : d289348 p = 1) (hb : d297878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289326 q = 1) (hb : d296187 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289326, d296187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76778 q ha hb
    | true =>
      simp only [d289326, d296187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76779 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289327 q = 1) (hb : d296188 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289327, d296188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289327, d296188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289328 q = 1) (hb : d297860 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289328, d297860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289328, d297860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289329 q = 1) (hb : d297861 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289329, d297861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289329, d297861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289333 q = 1) (hb : d297863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289333, d297863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289333, d297863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76780 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289334 q = 1) (hb : d297864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289334, d297864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289334, d297864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289335 q = 1) (hb : d297865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289335, d297865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289335, d297865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289336 q = 1) (hb : d297866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289336, d297866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289336, d297866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289337 q = 1) (hb : d297867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289337, d297867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289337, d297867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289343 q = 1) (hb : d297873 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289343, d297873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289343, d297873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76781 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289344 q = 1) (hb : d297874 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289344, d297874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289344, d297874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289345 q = 1) (hb : d297875 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289345, d297875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289345, d297875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289346 q = 1) (hb : d297876 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289346, d297876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289346, d297876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289347 q = 1) (hb : d297877 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289347, d297877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289347, d297877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289348 q = 1) (hb : d297878 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289348, d297878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289348, d297878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76783 (p : Pattern) (ha : d289354 p = 1) (hb : d297884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d289311 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74449 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d289312 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d289313 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d289314 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d289315 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289349 q = 1) (hb : d297879 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289349, d297879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289349, d297879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76782 q ha hb
  have h8 (q : Pattern) (ha : d289350 q = 1) (hb : d297880 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289350, d297880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289350, d297880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289351 q = 1) (hb : d297881 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289351, d297881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289351, d297881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289352 q = 1) (hb : d297882 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289352, d297882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289352, d297882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d289353 q = 1) (hb : d297883 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289353, d297883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289353, d297883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d289354 q = 1) (hb : d297884 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289354, d297884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d289354, d297884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro76784 (p : Pattern) (ha : d289359 p = 1) (hb : d296349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40481 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d296344 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289355 q = 1) (hb : d296345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289355, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289355, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40590 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289356 q = 1) (hb : d296346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289356, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289356, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d289357 q = 1) (hb : d296347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289357, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289357, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289358 q = 1) (hb : d296348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289358, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289358, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289359 q = 1) (hb : d296349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289359, d296349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289359, d296349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76785 (p : Pattern) (ha : d289364 p = 1) (hb : d296359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40481 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d296344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d289355 q = 1) (hb : d296345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289355, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289355, d296345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40590 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289356 q = 1) (hb : d296346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289356, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289356, d296346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d289357 q = 1) (hb : d296347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289357, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289357, d296347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289358 q = 1) (hb : d296348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289358, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289358, d296348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40600 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40605 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40607 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d296354 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d289360 q = 1) (hb : d296355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289360, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289360, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289361 q = 1) (hb : d296356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289361, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289361, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289362 q = 1) (hb : d296357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289362, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289362, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289363 q = 1) (hb : d296358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289363, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289363, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289364 q = 1) (hb : d296359 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289364, d296359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289364, d296359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76786 (p : Pattern) (ha : d289371 p = 1) (hb : d297887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d296354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289360 q = 1) (hb : d296355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289360, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289360, d296355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289361 q = 1) (hb : d296356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289361, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289361, d296356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289369 q = 1) (hb : d296357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289369, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289369, d296357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289370 q = 1) (hb : d296358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289370, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289370, d296358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289371 q = 1) (hb : d297887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289371, d297887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289371, d297887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76787 (p : Pattern) (ha : d289381 p = 1) (hb : d297898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289377 q = 1) (hb : d297894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289377, d297894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289377, d297894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289378 q = 1) (hb : d297895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289378, d297895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289378, d297895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289379 q = 1) (hb : d297896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289379, d297896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289379, d297896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289380 q = 1) (hb : d297897 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289380, d297897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289380, d297897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289381 q = 1) (hb : d297898 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289381, d297898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289381, d297898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76788 (p : Pattern) (ha : d289387 p = 1) (hb : d297904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40473 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289365 q = 1) (hb : d296360 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289365, d296360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76784 q ha hb
    | true =>
      simp only [d289365, d296360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76785 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289366 q = 1) (hb : d296361 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289366, d296361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289366, d296361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289367 q = 1) (hb : d297885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289367, d297885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289367, d297885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289368 q = 1) (hb : d297886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289368, d297886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289368, d297886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289372 q = 1) (hb : d297888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289372, d297888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289372, d297888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76786 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d40641 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289373 q = 1) (hb : d297889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289373, d297889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289373, d297889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289374 q = 1) (hb : d297890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289374, d297890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289374, d297890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289375 q = 1) (hb : d297891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289375, d297891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289375, d297891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289376 q = 1) (hb : d297892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289376, d297892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289376, d297892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289382 q = 1) (hb : d297899 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289382, d297899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289382, d297899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76787 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40746 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289383 q = 1) (hb : d297900 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289383, d297900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289383, d297900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289384 q = 1) (hb : d297901 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289384, d297901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289384, d297901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289385 q = 1) (hb : d297902 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289385, d297902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289385, d297902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289386 q = 1) (hb : d297903 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289386, d297903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289386, d297903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289387 q = 1) (hb : d297904 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289387, d297904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289387, d297904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76789 (p : Pattern) (ha : d289393 p = 1) (hb : d297910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289388 q = 1) (hb : d297905 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289388, d297905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289388, d297905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76788 q ha hb
  have h2 (q : Pattern) (ha : d289389 q = 1) (hb : d297906 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289389, d297906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289389, d297906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289390 q = 1) (hb : d297907 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289390, d297907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289390, d297907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289391 q = 1) (hb : d297908 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289391, d297908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289391, d297908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289392 q = 1) (hb : d297909 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289392, d297909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289392, d297909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289393 q = 1) (hb : d297910 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289393, d297910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289393, d297910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76790 (p : Pattern) (ha : d289399 p = 1) (hb : d296606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40820 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d40881 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d296601 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289395 q = 1) (hb : d296602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289395, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d289395, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d40954 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d289396 q = 1) (hb : d296603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289396, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d289396, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d289397 q = 1) (hb : d296604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289397, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289397, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d289398 q = 1) (hb : d296605 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289398, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289398, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d289399 q = 1) (hb : d296606 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289399, d296606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289399, d296606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76791 (p : Pattern) (ha : d289404 p = 1) (hb : d296616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40820 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d296601 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d289395 q = 1) (hb : d296602 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289395, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d289395, d296602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d40954 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d289396 q = 1) (hb : d296603 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289396, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289396, d296603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d289397 q = 1) (hb : d296604 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289397, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289397, d296604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289398 q = 1) (hb : d296605 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289398, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289398, d296605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d40964 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d40969 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d40971 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d296611 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d289400 q = 1) (hb : d296612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289400, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d289400, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d40978 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289401 q = 1) (hb : d296613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289401, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289401, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289402 q = 1) (hb : d296614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289402, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d289402, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d289403 q = 1) (hb : d296615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289403, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d289403, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d289404 q = 1) (hb : d296616 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289404, d296616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d289404, d296616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76792 (p : Pattern) (ha : d289411 p = 1) (hb : d297914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d40971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d296611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289400 q = 1) (hb : d296612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289400, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289400, d296612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d40978 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289401 q = 1) (hb : d296613 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289401, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289401, d296613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289409 q = 1) (hb : d296614 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289409, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289409, d296614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289410 q = 1) (hb : d296615 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289410, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289410, d296615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289411 q = 1) (hb : d297914 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289411, d297914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289411, d297914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76793 (p : Pattern) (ha : d289421 p = 1) (hb : d297925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41071 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297920 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289417 q = 1) (hb : d297921 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d289417, d297921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d289417, d297921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289418 q = 1) (hb : d297922 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d289418, d297922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289418, d297922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d289419 q = 1) (hb : d297923 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289419, d297923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289419, d297923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289420 q = 1) (hb : d297924 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d289420, d297924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289420, d297924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d289421 q = 1) (hb : d297925 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d289421, d297925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289421, d297925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76794 (p : Pattern) (ha : d289427 p = 1) (hb : d297931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d40812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289405 q = 1) (hb : d296617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289405, d296617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76790 q ha hb
    | true =>
      simp only [d289405, d296617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76791 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d40996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d289406 q = 1) (hb : d296618 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289406, d296618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289406, d296618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d289407 q = 1) (hb : d297912 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289407, d297912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d289407, d297912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289408 q = 1) (hb : d297913 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289408, d297913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d289408, d297913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d289412 q = 1) (hb : d297915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289412, d297915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289412, d297915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76792 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d41005 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d289413 q = 1) (hb : d297916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289413, d297916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d289413, d297916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d289414 q = 1) (hb : d297917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289414, d297917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d289414, d297917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289415 q = 1) (hb : d297918 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289415, d297918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d289415, d297918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d289416 q = 1) (hb : d297919 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289416, d297919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d289416, d297919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d289422 q = 1) (hb : d297926 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d289422, d297926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d289422, d297926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76793 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41142 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d289423 q = 1) (hb : d297927 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d289423, d297927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d289423, d297927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d289424 q = 1) (hb : d297928 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d289424, d297928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d289424, d297928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d289425 q = 1) (hb : d297929 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d289425, d297929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d289425, d297929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d289426 q = 1) (hb : d297930 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d289426, d297930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d289426, d297930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d289427 q = 1) (hb : d297931 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d289427, d297931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d289427, d297931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76795 (p : Pattern) (ha : d289433 p = 1) (hb : d297937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d289428 q = 1) (hb : d297932 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d289428, d297932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289428, d297932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76794 q ha hb
  have h2 (q : Pattern) (ha : d289429 q = 1) (hb : d297933 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d289429, d297933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289429, d297933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d289430 q = 1) (hb : d297934 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d289430, d297934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289430, d297934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d289431 q = 1) (hb : d297935 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d289431, d297935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289431, d297935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d289432 q = 1) (hb : d297936 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d289432, d297936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289432, d297936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289433 q = 1) (hb : d297937 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d289433, d297937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289433, d297937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76796 (p : Pattern) (ha : d290251 p = 1) (hb : d296900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d41307 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d296895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290247 q = 1) (hb : d296896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290247, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d290247, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d41417 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d290248 q = 1) (hb : d296897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290248, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290248, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d290249 q = 1) (hb : d296898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290249, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290249, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290250 q = 1) (hb : d296899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290250, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290250, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290251 q = 1) (hb : d296900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290251, d296900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290251, d296900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76797 (p : Pattern) (ha : d290256 p = 1) (hb : d296910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41307 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d296895 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d290247 q = 1) (hb : d296896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290247, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290247, d296896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d41417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d290248 q = 1) (hb : d296897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290248, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290248, d296897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d290249 q = 1) (hb : d296898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290249, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290249, d296898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290250 q = 1) (hb : d296899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290250, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290250, d296899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d41427 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d41432 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d41434 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d296905 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d290252 q = 1) (hb : d296906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290252, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d290252, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41441 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290253 q = 1) (hb : d296907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290253, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290253, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d290254 q = 1) (hb : d296908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290254, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d290254, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d290255 q = 1) (hb : d296909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290255, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d290255, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d290256 q = 1) (hb : d296910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290256, d296910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d290256, d296910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76798 (p : Pattern) (ha : d290263 p = 1) (hb : d297942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41434 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d296905 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290252 q = 1) (hb : d296906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290252, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290252, d296906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41441 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290253 q = 1) (hb : d296907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290253, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290253, d296907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d290261 q = 1) (hb : d296908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290261, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290261, d296908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290262 q = 1) (hb : d296909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290262, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290262, d296909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290263 q = 1) (hb : d297942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290263, d297942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290263, d297942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76799 (p : Pattern) (ha : d290273 p = 1) (hb : d297953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297948 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290269 q = 1) (hb : d297949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290269, d297949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290269, d297949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41625 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290270 q = 1) (hb : d297950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290270, d297950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290270, d297950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d290271 q = 1) (hb : d297951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290271, d297951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290271, d297951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290272 q = 1) (hb : d297952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290272, d297952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290272, d297952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290273 q = 1) (hb : d297953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290273, d297953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290273, d297953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76800 (p : Pattern) (ha : d290279 p = 1) (hb : d297959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41247 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290257 q = 1) (hb : d296911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290257, d296911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76796 q ha hb
    | true =>
      simp only [d290257, d296911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76797 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290258 q = 1) (hb : d296912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290258, d296912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290258, d296912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290259 q = 1) (hb : d297940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290259, d297940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290259, d297940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290260 q = 1) (hb : d297941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290260, d297941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290260, d297941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290264 q = 1) (hb : d297943 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290264, d297943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290264, d297943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76798 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d41468 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d290265 q = 1) (hb : d297944 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290265, d297944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290265, d297944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d290266 q = 1) (hb : d297945 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290266, d297945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290266, d297945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d290267 q = 1) (hb : d297946 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290267, d297946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290267, d297946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d290268 q = 1) (hb : d297947 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290268, d297947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290268, d297947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d290274 q = 1) (hb : d297954 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290274, d297954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290274, d297954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76799 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41641 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290275 q = 1) (hb : d297955 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290275, d297955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290275, d297955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d290276 q = 1) (hb : d297956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290276, d297956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290276, d297956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d290277 q = 1) (hb : d297957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290277, d297957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d290277, d297957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d290278 q = 1) (hb : d297958 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290278, d297958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d290278, d297958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d290279 q = 1) (hb : d297959 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290279, d297959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290279, d297959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76801 (p : Pattern) (ha : d290285 p = 1) (hb : d297965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290280 q = 1) (hb : d297960 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290280, d297960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290280, d297960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76800 q ha hb
  have h2 (q : Pattern) (ha : d290281 q = 1) (hb : d297961 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290281, d297961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290281, d297961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290282 q = 1) (hb : d297962 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290282, d297962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290282, d297962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290283 q = 1) (hb : d297963 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290283, d297963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290283, d297963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290284 q = 1) (hb : d297964 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290284, d297964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290284, d297964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290285 q = 1) (hb : d297965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290285, d297965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290285, d297965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76802 (p : Pattern) (ha : d290293 p = 1) (hb : d297245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d41821 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d297240 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290289 q = 1) (hb : d297241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290289, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d290289, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d41951 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d290290 q = 1) (hb : d297242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290290, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290290, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d290291 q = 1) (hb : d297243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290291, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290291, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290292 q = 1) (hb : d297244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290292, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290292, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290293 q = 1) (hb : d297245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290293, d297245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290293, d297245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76803 (p : Pattern) (ha : d290298 p = 1) (hb : d297255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41782 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41821 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d297240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d290289 q = 1) (hb : d297241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290289, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290289, d297241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d41951 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d290290 q = 1) (hb : d297242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290290, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290290, d297242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d290291 q = 1) (hb : d297243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290291, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290291, d297243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290292 q = 1) (hb : d297244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290292, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290292, d297244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d41961 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d41966 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d41968 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d297250 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d290294 q = 1) (hb : d297251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290294, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d290294, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d41975 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290295 q = 1) (hb : d297252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290295, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290295, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d290296 q = 1) (hb : d297253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290296, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d290296, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d290297 q = 1) (hb : d297254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290297, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d290297, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d290298 q = 1) (hb : d297255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290298, d297255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d290298, d297255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76804 (p : Pattern) (ha : d290305 p = 1) (hb : d297971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d41968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290294 q = 1) (hb : d297251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290294, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290294, d297251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d41975 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290295 q = 1) (hb : d297252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290295, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290295, d297252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d290303 q = 1) (hb : d297253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290303, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290303, d297253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290304 q = 1) (hb : d297254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290304, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290304, d297254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290305 q = 1) (hb : d297971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290305, d297971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290305, d297971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76805 (p : Pattern) (ha : d290315 p = 1) (hb : d297982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290311 q = 1) (hb : d297978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290311, d297978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290311, d297978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290312 q = 1) (hb : d297979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290312, d297979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290312, d297979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d290313 q = 1) (hb : d297980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290313, d297980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290313, d297980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290314 q = 1) (hb : d297981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290314, d297981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290314, d297981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290315 q = 1) (hb : d297982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290315, d297982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290315, d297982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76806 (p : Pattern) (ha : d290321 p = 1) (hb : d297988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d41774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290299 q = 1) (hb : d297256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290299, d297256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76802 q ha hb
    | true =>
      simp only [d290299, d297256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d41993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d290300 q = 1) (hb : d297257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290300, d297257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290300, d297257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d290301 q = 1) (hb : d297969 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290301, d297969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290301, d297969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290302 q = 1) (hb : d297970 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290302, d297970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290302, d297970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290306 q = 1) (hb : d297972 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290306, d297972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290306, d297972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76804 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42002 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d290307 q = 1) (hb : d297973 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290307, d297973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290307, d297973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d290308 q = 1) (hb : d297974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290308, d297974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290308, d297974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d290309 q = 1) (hb : d297975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290309, d297975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290309, d297975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d290310 q = 1) (hb : d297976 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290310, d297976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290310, d297976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d290316 q = 1) (hb : d297983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290316, d297983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290316, d297983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76805 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42186 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d290317 q = 1) (hb : d297984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290317, d297984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290317, d297984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d290318 q = 1) (hb : d297985 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290318, d297985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290318, d297985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d290319 q = 1) (hb : d297986 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290319, d297986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d290319, d297986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d290320 q = 1) (hb : d297987 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290320, d297987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d290320, d297987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d290321 q = 1) (hb : d297988 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290321, d297988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290321, d297988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76807 (p : Pattern) (ha : d290327 p = 1) (hb : d297994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290322 q = 1) (hb : d297989 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290322, d297989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290322, d297989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76806 q ha hb
  have h2 (q : Pattern) (ha : d290323 q = 1) (hb : d297990 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290323, d297990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290323, d297990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290324 q = 1) (hb : d297991 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290324, d297991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290324, d297991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290325 q = 1) (hb : d297992 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290325, d297992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290325, d297992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290326 q = 1) (hb : d297993 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290326, d297993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290326, d297993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290327 q = 1) (hb : d297994 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290327, d297994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290327, d297994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76808 (p : Pattern) (ha : d290333 p = 1) (hb : d298030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d289394 q = 1) (hb : d297911 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289394, d297911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76783 q ha hb
    | true =>
      simp only [d289394, d297911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76789 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d289434 q = 1) (hb : d297938 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d289434, d297938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d289434, d297938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76795 q ha hb
  have h3 (q : Pattern) (ha : d289435 q = 1) (hb : d297939 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d289435, d297939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289435, d297939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290286 q = 1) (hb : d297966 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290286, d297966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290286, d297966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76801 q ha hb
  have h5 (q : Pattern) (ha : d290287 q = 1) (hb : d297967 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290287, d297967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290287, d297967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290288 q = 1) (hb : d297968 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290288, d297968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290288, d297968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290328 q = 1) (hb : d297995 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290328, d297995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290328, d297995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76807 q ha hb
  have h8 (q : Pattern) (ha : d290329 q = 1) (hb : d297996 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290329, d297996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290329, d297996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290330 q = 1) (hb : d297997 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290330, d297997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290330, d297997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290331 q = 1) (hb : d297998 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290331, d297998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290331, d297998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d281058 q = 1) (hb : d298025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d281058, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281058, d298025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76777 q ha hb
  have h12 (q : Pattern) (ha : d281059 q = 1) (hb : d298026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d281059, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281059, d298026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d281060 q = 1) (hb : d298027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d281060, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281060, d298027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d281061 q = 1) (hb : d298028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d281061, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d281061, d298028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d290332 q = 1) (hb : d298029 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290332, d298029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290332, d298029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290333 q = 1) (hb : d298030 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290333, d298030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290333, d298030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro76809 (p : Pattern) (ha : d290339 p = 1) (hb : d298036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290334 q = 1) (hb : d298031 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290334, d298031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76808 q ha hb
    | true =>
      simp only [d290334, d298031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290335 q = 1) (hb : d298032 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290335, d298032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290335, d298032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290336 q = 1) (hb : d298033 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290336, d298033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290336, d298033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290337 q = 1) (hb : d298034 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290337, d298034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290337, d298034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290338 q = 1) (hb : d298035 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290338, d298035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290338, d298035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290339 q = 1) (hb : d298036 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290339, d298036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290339, d298036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76810 (p : Pattern) (ha : d290345 p = 1) (hb : d298042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290340 q = 1) (hb : d298037 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290340, d298037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76809 q ha hb
    | true =>
      simp only [d290340, d298037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290341 q = 1) (hb : d298038 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290341, d298038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290341, d298038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290342 q = 1) (hb : d298039 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290342, d298039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290342, d298039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290343 q = 1) (hb : d298040 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290343, d298040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290343, d298040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290344 q = 1) (hb : d298041 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290344, d298041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290344, d298041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290345 q = 1) (hb : d298042 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290345, d298042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290345, d298042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76811 (p : Pattern) (ha : d290351 p = 1) (hb : d298048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290346 q = 1) (hb : d298043 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290346, d298043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76810 q ha hb
    | true =>
      simp only [d290346, d298043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290347 q = 1) (hb : d298044 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290347, d298044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290347, d298044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290348 q = 1) (hb : d298045 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290348, d298045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290348, d298045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290349 q = 1) (hb : d298046 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290349, d298046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290349, d298046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290350 q = 1) (hb : d298047 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290350, d298047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290350, d298047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290351 q = 1) (hb : d298048 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290351, d298048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290351, d298048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76812 (p : Pattern) (ha : d290357 p = 1) (hb : d298054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290352 q = 1) (hb : d298049 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290352, d298049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76811 q ha hb
    | true =>
      simp only [d290352, d298049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290353 q = 1) (hb : d298050 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290353, d298050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290353, d298050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290354 q = 1) (hb : d298051 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290354, d298051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290354, d298051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290355 q = 1) (hb : d298052 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290355, d298052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290355, d298052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290356 q = 1) (hb : d298053 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290356, d298053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290356, d298053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290357 q = 1) (hb : d298054 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290357, d298054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290357, d298054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76813 (p : Pattern) (ha : d290363 p = 1) (hb : d298060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290358 q = 1) (hb : d298055 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290358, d298055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76812 q ha hb
    | true =>
      simp only [d290358, d298055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290359 q = 1) (hb : d298056 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290359, d298056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290359, d298056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290360 q = 1) (hb : d298057 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290360, d298057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290360, d298057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290361 q = 1) (hb : d298058 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290361, d298058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290361, d298058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290362 q = 1) (hb : d298059 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290362, d298059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290362, d298059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290363 q = 1) (hb : d298060 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290363, d298060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290363, d298060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76814 (p : Pattern) (ha : d290369 p = 1) (hb : d298066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290364 q = 1) (hb : d298061 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290364, d298061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76813 q ha hb
    | true =>
      simp only [d290364, d298061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290365 q = 1) (hb : d298062 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290365, d298062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290365, d298062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290366 q = 1) (hb : d298063 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290366, d298063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290366, d298063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290367 q = 1) (hb : d298064 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290367, d298064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290367, d298064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290368 q = 1) (hb : d298065 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290368, d298065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290368, d298065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290369 q = 1) (hb : d298066 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290369, d298066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290369, d298066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76815 (p : Pattern) (ha : d290375 p = 1) (hb : d298072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290370 q = 1) (hb : d298067 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290370, d298067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76814 q ha hb
    | true =>
      simp only [d290370, d298067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290371 q = 1) (hb : d298068 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290371, d298068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290371, d298068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290372 q = 1) (hb : d298069 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290372, d298069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290372, d298069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290373 q = 1) (hb : d298070 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290373, d298070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290373, d298070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290374 q = 1) (hb : d298071 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290374, d298071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290374, d298071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290375 q = 1) (hb : d298072 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290375, d298072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290375, d298072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76816 (p : Pattern) (ha : d30638 p = 1) (hb : d261985 p = 1) : d298076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d261985 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30636 q = 1) (hb : d261985 q = 1) : d298074 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30637 q = 1) (hb : d261985 q = 1) : d298075 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d261985 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d30638 q = 1) (hb : d261985 q = 1) : d298076 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30638, d298076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30638, d298076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro76817 (p : Pattern) (ha : d30644 p = 1) (hb : d261985 p = 1) : d298082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30639 q = 1) (hb : d261985 q = 1) : d298077 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
    | true =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30640 q = 1) (hb : d261985 q = 1) : d298078 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30641 q = 1) (hb : d261985 q = 1) : d298079 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d298079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d298079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30642 q = 1) (hb : d261985 q = 1) : d298080 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d298080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30642, d298080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d261985 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30643 q = 1) (hb : d261985 q = 1) : d298081 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30643, d298081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30643, d298081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d261985 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30644 q = 1) (hb : d261985 q = 1) : d298082 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30644, d298082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30644, d298082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76818 (p : Pattern) (ha : d30650 p = 1) (hb : d261985 p = 1) : d298088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d261985 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30645 q = 1) (hb : d261985 q = 1) : d298083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
    | true =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30646 q = 1) (hb : d261985 q = 1) : d298084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30647 q = 1) (hb : d261985 q = 1) : d298085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d261985 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30648 q = 1) (hb : d261985 q = 1) : d298086 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d298086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30648, d298086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d261985 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30649 q = 1) (hb : d261985 q = 1) : d298087 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30649, d298087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30649, d298087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30650 q = 1) (hb : d261985 q = 1) : d298088 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30650, d298088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30650, d298088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro76819 (p : Pattern) (ha : d30656 p = 1) (hb : d261985 p = 1) : d298094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d261985 q = 1) : d298092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d261985 q = 1) : d298093 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d298093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d298093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30656 q = 1) (hb : d261985 q = 1) : d298094 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30656, d298094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30656, d298094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro76820 (p : Pattern) (ha : d245354 p = 1) (hb : d261985 p = 1) : d298100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d261985 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d261985 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d261985 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30657 q = 1) (hb : d261985 q = 1) : d298095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
    | true =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245350 q = 1) (hb : d261985 q = 1) : d298096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d298096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245350, d298096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d261985 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245351 q = 1) (hb : d261985 q = 1) : d298097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d298097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d298097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245352 q = 1) (hb : d261985 q = 1) : d298098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d298098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245352, d298098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245353 q = 1) (hb : d261985 q = 1) : d298099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d298099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245353, d298099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245354 q = 1) (hb : d261985 q = 1) : d298100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245354, d298100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245354, d298100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76821 (p : Pattern) (ha : d30663 p = 1) (hb : d261985 p = 1) : d298101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d261985 q = 1) : d298092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d261985 q = 1) : d298093 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d298093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d298093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30663 q = 1) (hb : d261985 q = 1) : d298101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30663, d298101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30663, d298101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76822 (p : Pattern) (ha : d245359 p = 1) (hb : d261985 p = 1) : d298107 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d261985 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d261985 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d261985 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30657 q = 1) (hb : d261985 q = 1) : d298095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
    | true =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245350 q = 1) (hb : d261985 q = 1) : d298096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d298096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245350, d298096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d261985 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d245351 q = 1) (hb : d261985 q = 1) : d298097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d298097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d298097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245352 q = 1) (hb : d261985 q = 1) : d298098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d298098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245352, d298098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245353 q = 1) (hb : d261985 q = 1) : d298099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d298099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245353, d298099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d261985 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d261985 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d261985 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30664 q = 1) (hb : d261985 q = 1) : d298102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76821 q ha hb
    | true =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245355 q = 1) (hb : d261985 q = 1) : d298103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d298103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245355, d298103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d261985 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d245356 q = 1) (hb : d261985 q = 1) : d298104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d298104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245356, d298104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245357 q = 1) (hb : d261985 q = 1) : d298105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245357, d298105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245357, d298105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245358 q = 1) (hb : d261985 q = 1) : d298106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245358, d298106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245358, d298106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d245359 q = 1) (hb : d261985 q = 1) : d298107 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245359, d298107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245359, d298107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76823 (p : Pattern) (ha : d245366 p = 1) (hb : d261985 p = 1) : d298114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d261985 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30664 q = 1) (hb : d261985 q = 1) : d298102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76821 q ha hb
    | true =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245355 q = 1) (hb : d261985 q = 1) : d298103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d298103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245355, d298103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d261985 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245356 q = 1) (hb : d261985 q = 1) : d298104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d298104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245356, d298104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245364 q = 1) (hb : d261985 q = 1) : d298112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245364, d298112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245364, d298112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245365 q = 1) (hb : d261985 q = 1) : d298113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245365, d298113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245365, d298113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245366 q = 1) (hb : d261985 q = 1) : d298114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245366, d298114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245366, d298114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76824 (p : Pattern) (ha : d30687 p = 1) (hb : d261985 p = 1) : d298125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30682 q = 1) (hb : d261985 q = 1) : d298120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d298120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d298120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
  have h2 (q : Pattern) (ha : d30639 q = 1) (hb : d261985 q = 1) : d298077 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
    | true =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30683 q = 1) (hb : d261985 q = 1) : d298121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d298121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30683, d298121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30640 q = 1) (hb : d261985 q = 1) : d298078 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30684 q = 1) (hb : d261985 q = 1) : d298122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d298122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30684, d298122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30685 q = 1) (hb : d261985 q = 1) : d298123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d298123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30685, d298123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d261985 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30686 q = 1) (hb : d261985 q = 1) : d298124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30686, d298124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30686, d298124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d261985 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30687 q = 1) (hb : d261985 q = 1) : d298125 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30687, d298125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30687, d298125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76825 (p : Pattern) (ha : d30693 p = 1) (hb : d261985 p = 1) : d298131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d261985 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30688 q = 1) (hb : d261985 q = 1) : d298126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
    | true =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30689 q = 1) (hb : d261985 q = 1) : d298127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30690 q = 1) (hb : d261985 q = 1) : d298128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d261985 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30691 q = 1) (hb : d261985 q = 1) : d298129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d298129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30691, d298129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d261985 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30692 q = 1) (hb : d261985 q = 1) : d298130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30692, d298130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30692, d298130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30693 q = 1) (hb : d261985 q = 1) : d298131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30693, d298131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30693, d298131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro76826 (p : Pattern) (ha : d30699 p = 1) (hb : d261985 p = 1) : d298137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d261985 q = 1) : d298132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76825 q ha hb
    | true =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d261985 q = 1) : d298133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d261985 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30696 q = 1) (hb : d261985 q = 1) : d298134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30696, d298134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30696, d298134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30697 q = 1) (hb : d261985 q = 1) : d298135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30697, d298135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30697, d298135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30698 q = 1) (hb : d261985 q = 1) : d298136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30698, d298136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30698, d298136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30699 q = 1) (hb : d261985 q = 1) : d298137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30699, d298137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30699, d298137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76827 (p : Pattern) (ha : d245376 p = 1) (hb : d261985 p = 1) : d298143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d261985 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30700 q = 1) (hb : d261985 q = 1) : d298138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76826 q ha hb
    | true =>
      simp only [d30700, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245372 q = 1) (hb : d261985 q = 1) : d298139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245372, d298139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245372, d298139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d261985 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245373 q = 1) (hb : d261985 q = 1) : d298140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245373, d298140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245373, d298140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245374 q = 1) (hb : d261985 q = 1) : d298141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245374, d298141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245374, d298141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245375 q = 1) (hb : d261985 q = 1) : d298142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245375, d298142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245375, d298142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245376 q = 1) (hb : d261985 q = 1) : d298143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245376, d298143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245376, d298143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76828 (p : Pattern) (ha : d245382 p = 1) (hb : d261985 p = 1) : d298149 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d261985 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245360 q = 1) (hb : d261985 q = 1) : d298108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245360, d298108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76820 q ha hb
    | true =>
      simp only [d245360, d298108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76822 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d261985 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245361 q = 1) (hb : d261985 q = 1) : d298109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245361, d298109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245361, d298109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d245362 q = 1) (hb : d261985 q = 1) : d298110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245362, d298110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245362, d298110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245363 q = 1) (hb : d261985 q = 1) : d298111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245363, d298111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245363, d298111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245367 q = 1) (hb : d261985 q = 1) : d298115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245367, d298115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245367, d298115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76823 q ha hb
  have h8 (q : Pattern) (ha : d245368 q = 1) (hb : d261985 q = 1) : d298116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245368, d298116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245368, d298116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d245369 q = 1) (hb : d261985 q = 1) : d298117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245369, d298117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245369, d298117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d245370 q = 1) (hb : d261985 q = 1) : d298118 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245370, d298118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245370, d298118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d245371 q = 1) (hb : d261985 q = 1) : d298119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245371, d298119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245371, d298119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245377 q = 1) (hb : d261985 q = 1) : d298144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245377, d298144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245377, d298144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76827 q ha hb
  have h13 (q : Pattern) (ha : d245378 q = 1) (hb : d261985 q = 1) : d298145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245378, d298145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245378, d298145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d245379 q = 1) (hb : d261985 q = 1) : d298146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245379, d298146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245379, d298146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d245380 q = 1) (hb : d261985 q = 1) : d298147 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245380, d298147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245380, d298147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d245381 q = 1) (hb : d261985 q = 1) : d298148 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245381, d298148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245381, d298148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d245382 q = 1) (hb : d261985 q = 1) : d298149 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245382, d298149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245382, d298149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro76829 (p : Pattern) (ha : d30721 p = 1) (hb : d261985 p = 1) : d298159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d261985 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d261985 q = 1) : d298095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
    | true =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d261985 q = 1) : d298155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d261985 q = 1) : d298156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d261985 q = 1) : d298157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d261985 q = 1) : d298158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30721 q = 1) (hb : d261985 q = 1) : d298159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30721, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30721, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro76830 (p : Pattern) (ha : d30728 p = 1) (hb : d261985 p = 1) : d298166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d261985 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d261985 q = 1) : d298095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
    | true =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d261985 q = 1) : d298155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d261985 q = 1) : d298156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d261985 q = 1) : d298157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d261985 q = 1) : d298158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d261985 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30664 q = 1) (hb : d261985 q = 1) : d298102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76821 q ha hb
    | true =>
      simp only [d30664, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30724 q = 1) (hb : d261985 q = 1) : d298162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30725 q = 1) (hb : d261985 q = 1) : d298163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30725, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30726 q = 1) (hb : d261985 q = 1) : d298164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30727 q = 1) (hb : d261985 q = 1) : d298165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30728 q = 1) (hb : d261985 q = 1) : d298166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30728, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30728, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro76831 (p : Pattern) (ha : d30834 p = 1) (hb : d261985 p = 1) : d298244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d261985 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d261985 q = 1) : d298095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
    | true =>
      simp only [d30657, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d261985 q = 1) : d298155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d261985 q = 1) : d298156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d261985 q = 1) : d298157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d261985 q = 1) : d298158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d261985 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30834 q = 1) (hb : d261985 q = 1) : d298244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30834, d298244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30834, d298244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76832 (p : Pattern) (ha : d30733 p = 1) (hb : d261985 p = 1) : d298171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d261985 q = 1) : d298092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30732 q = 1) (hb : d261985 q = 1) : d298170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d298170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d298170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30733 q = 1) (hb : d261985 q = 1) : d298171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30733, d298171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30733, d298171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro76833 (p : Pattern) (ha : d30740 p = 1) (hb : d261985 p = 1) : d298178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30738 q = 1) (hb : d261985 q = 1) : d298176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d298176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d298176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30739 q = 1) (hb : d261985 q = 1) : d298177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d298177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30739, d298177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30740 q = 1) (hb : d261985 q = 1) : d298178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30740, d298178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30740, d298178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro76834 (p : Pattern) (ha : d30744 p = 1) (hb : d261985 p = 1) : d264156 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d310 q = 1) : d310 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d311 q = 1) (hb : d261984 q = 1) : d33326 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d311, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30744 q = 1) (hb : d261985 q = 1) : d264156 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30744, d261985, d264156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30744, d261985, d264156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro76835 (p : Pattern) (ha : d30750 p = 1) (hb : d261985 p = 1) : d298185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30748 q = 1) (hb : d261985 q = 1) : d298183 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30749 q = 1) (hb : d261985 q = 1) : d298184 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d261985 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30636 q = 1) (hb : d261985 q = 1) : d298074 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30637 q = 1) (hb : d261985 q = 1) : d298075 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30750 q = 1) (hb : d261985 q = 1) : d298185 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30750, d298185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30750, d298185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro76836 (p : Pattern) (ha : d30758 p = 1) (hb : d261985 p = 1) : d298193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30756 q = 1) (hb : d261985 q = 1) : d298191 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30757 q = 1) (hb : d261985 q = 1) : d298192 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d261985 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30758 q = 1) (hb : d261985 q = 1) : d298193 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30758, d298193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30758, d298193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76837 (p : Pattern) (ha : d30764 p = 1) (hb : d261985 p = 1) : d298199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d261985 q = 1) : d298186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
    | true =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d261985 q = 1) : d298187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d261985 q = 1) : d298188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d298188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d298188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d261985 q = 1) : d298189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d298189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d298189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30639 q = 1) (hb : d261985 q = 1) : d298077 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
    | true =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30640 q = 1) (hb : d261985 q = 1) : d298078 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30641 q = 1) (hb : d261985 q = 1) : d298079 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d298079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d298079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30642 q = 1) (hb : d261985 q = 1) : d298080 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d298080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30642, d298080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30755 q = 1) (hb : d261985 q = 1) : d298190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30755, d298190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30755, d298190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30761 q = 1) (hb : d261985 q = 1) : d298196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30762 q = 1) (hb : d261985 q = 1) : d298197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d261985 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d30763 q = 1) (hb : d261985 q = 1) : d298198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30763, d298198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30763, d298198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30764 q = 1) (hb : d261985 q = 1) : d298199 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30764, d298199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30764, d298199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro76838 (p : Pattern) (ha : d30770 p = 1) (hb : d261985 p = 1) : d298205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d261985 q = 1) : d298200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76837 q ha hb
    | true =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d261985 q = 1) : d298201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d261985 q = 1) : d298202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d261985 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30645 q = 1) (hb : d261985 q = 1) : d298083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
    | true =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30646 q = 1) (hb : d261985 q = 1) : d298084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30647 q = 1) (hb : d261985 q = 1) : d298085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30768 q = 1) (hb : d261985 q = 1) : d298203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d261985 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30648 q = 1) (hb : d261985 q = 1) : d298086 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d298086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30648, d298086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30769 q = 1) (hb : d261985 q = 1) : d298204 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30769, d298204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30769, d298204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30770 q = 1) (hb : d261985 q = 1) : d298205 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30770, d298205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30770, d298205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro76839 (p : Pattern) (ha : d30776 p = 1) (hb : d261985 p = 1) : d298211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d261985 q = 1) : d298206 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d298206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76838 q ha hb
    | true =>
      simp only [d30771, d298206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d261985 q = 1) : d298207 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d298207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d298207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d261985 q = 1) : d298208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d298208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d298208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d261985 q = 1) : d298209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d298209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d298209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d261985 q = 1) : d298210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d298210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d298210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30776 q = 1) (hb : d261985 q = 1) : d298211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30776, d298211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30776, d298211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76840 (p : Pattern) (ha : d30805 p = 1) (hb : d261985 p = 1) : d298217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d261985 q = 1) : d298214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d298214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d298214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d261985 q = 1) : d298215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d298215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d298215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d261985 q = 1) : d298216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d298216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d298216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30805 q = 1) (hb : d261985 q = 1) : d298217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30805, d298217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30805, d298217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76841 (p : Pattern) (ha : d245392 p = 1) (hb : d261985 p = 1) : d298223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d261985 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30734 q = 1) (hb : d261985 q = 1) : d298172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d298172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76832 q ha hb
    | true =>
      simp only [d30734, d298172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30735 q = 1) (hb : d261985 q = 1) : d298173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d298173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d298173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30736 q = 1) (hb : d261985 q = 1) : d298174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d298174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30736, d298174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30737 q = 1) (hb : d261985 q = 1) : d298175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d298175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d298175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d261985 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30741 q = 1) (hb : d261985 q = 1) : d298179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d298179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76833 q ha hb
    | true =>
      simp only [d30741, d298179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30742 q = 1) (hb : d261985 q = 1) : d298180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d298180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d298180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30743 q = 1) (hb : d261985 q = 1) : d298181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d298181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30743, d298181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30777 q = 1) (hb : d261985 q = 1) : d298212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d298212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76839 q ha hb
    | true =>
      simp only [d30777, d298212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
  have h11 (q : Pattern) (ha : d245388 q = 1) (hb : d261985 q = 1) : d298213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d298213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245388, d298213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30806 q = 1) (hb : d261985 q = 1) : d298218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d298218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76840 q ha hb
    | true =>
      simp only [d30806, d298218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30807 q = 1) (hb : d261985 q = 1) : d298219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d298219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30807, d298219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245389 q = 1) (hb : d261985 q = 1) : d298220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d298220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245389, d298220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245390 q = 1) (hb : d261985 q = 1) : d298221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d298221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245390, d298221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245391 q = 1) (hb : d261985 q = 1) : d298222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d298222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245391, d298222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245392 q = 1) (hb : d261985 q = 1) : d298223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d298223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245392, d298223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro76842 (p : Pattern) (ha : d30812 p = 1) (hb : d261985 p = 1) : d298224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d261985 q = 1) : d298092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d298092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30732 q = 1) (hb : d261985 q = 1) : d298170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d298170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d298170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30812 q = 1) (hb : d261985 q = 1) : d298224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30812, d298224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30812, d298224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76843 (p : Pattern) (ha : d30817 p = 1) (hb : d261985 p = 1) : d298229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d261985 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d261985 q = 1) : d298091 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d298091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30738 q = 1) (hb : d261985 q = 1) : d298176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d298176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d298176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30739 q = 1) (hb : d261985 q = 1) : d298177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d298177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30739, d298177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30817 q = 1) (hb : d261985 q = 1) : d298229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30817, d298229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30817, d298229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76844 (p : Pattern) (ha : d30821 p = 1) (hb : d261985 p = 1) : d298233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d261985 q = 1) : d298206 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d298206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76838 q ha hb
    | true =>
      simp only [d30771, d298206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d261985 q = 1) : d298207 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d298207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d298207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d261985 q = 1) : d298208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d298208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d298208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d261985 q = 1) : d298209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d298209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d298209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d261985 q = 1) : d298210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d298210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d298210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30821 q = 1) (hb : d261985 q = 1) : d298233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30821, d298233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30821, d298233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76845 (p : Pattern) (ha : d30826 p = 1) (hb : d261985 p = 1) : d298236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d261985 q = 1) : d298089 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76818 q ha hb
    | true =>
      simp only [d30651, d298089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d261985 q = 1) : d298090 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d298090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d261985 q = 1) : d298214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d298214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d298214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d261985 q = 1) : d298215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d298215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d298215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d261985 q = 1) : d298216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d298216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d298216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30826 q = 1) (hb : d261985 q = 1) : d298236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30826, d298236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30826, d298236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76846 (p : Pattern) (ha : d245397 p = 1) (hb : d261985 p = 1) : d298242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d261985 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30734 q = 1) (hb : d261985 q = 1) : d298172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d298172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76832 q ha hb
    | true =>
      simp only [d30734, d298172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30735 q = 1) (hb : d261985 q = 1) : d298173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d298173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d298173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30736 q = 1) (hb : d261985 q = 1) : d298174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d298174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30736, d298174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30737 q = 1) (hb : d261985 q = 1) : d298175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d298175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d298175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d261985 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30741 q = 1) (hb : d261985 q = 1) : d298179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d298179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76833 q ha hb
    | true =>
      simp only [d30741, d298179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30742 q = 1) (hb : d261985 q = 1) : d298180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d298180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d298180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30743 q = 1) (hb : d261985 q = 1) : d298181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d298181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30743, d298181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30777 q = 1) (hb : d261985 q = 1) : d298212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d298212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76839 q ha hb
    | true =>
      simp only [d30777, d298212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76819 q ha hb
  have h11 (q : Pattern) (ha : d245388 q = 1) (hb : d261985 q = 1) : d298213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d298213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245388, d298213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30806 q = 1) (hb : d261985 q = 1) : d298218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d298218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76840 q ha hb
    | true =>
      simp only [d30806, d298218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30807 q = 1) (hb : d261985 q = 1) : d298219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d298219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30807, d298219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245389 q = 1) (hb : d261985 q = 1) : d298220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d298220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245389, d298220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245390 q = 1) (hb : d261985 q = 1) : d298221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d298221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245390, d298221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245391 q = 1) (hb : d261985 q = 1) : d298222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d298222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245391, d298222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d261985 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d30813 q = 1) (hb : d261985 q = 1) : d298225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30813, d298225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76842 q ha hb
    | true =>
      simp only [d30813, d298225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30814 q = 1) (hb : d261985 q = 1) : d298226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30814, d298226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30814, d298226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d30815 q = 1) (hb : d261985 q = 1) : d298227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30815, d298227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d30815, d298227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d30816 q = 1) (hb : d261985 q = 1) : d298228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30816, d298228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30816, d298228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d261985 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d30818 q = 1) (hb : d261985 q = 1) : d298230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30818, d298230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76843 q ha hb
    | true =>
      simp only [d30818, d298230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d30819 q = 1) (hb : d261985 q = 1) : d298231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30819, d298231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30819, d298231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d30820 q = 1) (hb : d261985 q = 1) : d298232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30820, d298232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d30820, d298232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d30822 q = 1) (hb : d261985 q = 1) : d298234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d298234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76844 q ha hb
    | true =>
      simp only [d30822, d298234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76821 q ha hb
  have h27 (q : Pattern) (ha : d245393 q = 1) (hb : d261985 q = 1) : d298235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d298235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d245393, d298235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d30827 q = 1) (hb : d261985 q = 1) : d298237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d298237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76845 q ha hb
    | true =>
      simp only [d30827, d298237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d30828 q = 1) (hb : d261985 q = 1) : d298238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d298238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d30828, d298238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d245394 q = 1) (hb : d261985 q = 1) : d298239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d298239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d245394, d298239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d245395 q = 1) (hb : d261985 q = 1) : d298240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d298240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d245395, d298240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d245396 q = 1) (hb : d261985 q = 1) : d298241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d298241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245396, d298241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d245397 q = 1) (hb : d261985 q = 1) : d298242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d298242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245397, d298242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro76847 (p : Pattern) (ha : d245404 p = 1) (hb : d261985 p = 1) : d298251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30822 q = 1) (hb : d261985 q = 1) : d298234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d298234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76844 q ha hb
    | true =>
      simp only [d30822, d298234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76821 q ha hb
  have h2 (q : Pattern) (ha : d245393 q = 1) (hb : d261985 q = 1) : d298235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d298235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245393, d298235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30827 q = 1) (hb : d261985 q = 1) : d298237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d298237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76845 q ha hb
    | true =>
      simp only [d30827, d298237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30828 q = 1) (hb : d261985 q = 1) : d298238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d298238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30828, d298238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245394 q = 1) (hb : d261985 q = 1) : d298239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d298239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245394, d298239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245402 q = 1) (hb : d261985 q = 1) : d298249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d298249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245402, d298249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245403 q = 1) (hb : d261985 q = 1) : d298250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d298250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245403, d298250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d261985 q = 1) : d298251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d298251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d298251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76848 (p : Pattern) (ha : d30857 p = 1) (hb : d261985 p = 1) : d298267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d261985 q = 1) : d298257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d298257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d298257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d261985 q = 1) : d298186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
    | true =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d261985 q = 1) : d298258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d298258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d298258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d261985 q = 1) : d298187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d261985 q = 1) : d298259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d298259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d298259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d261985 q = 1) : d298260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d298260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d298260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30682 q = 1) (hb : d261985 q = 1) : d298120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d298120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d298120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
  have h8 (q : Pattern) (ha : d30639 q = 1) (hb : d261985 q = 1) : d298077 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76816 q ha hb
    | true =>
      simp only [d30639, d298077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30683 q = 1) (hb : d261985 q = 1) : d298121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d298121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30683, d298121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30640 q = 1) (hb : d261985 q = 1) : d298078 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30640, d298078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30684 q = 1) (hb : d261985 q = 1) : d298122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d298122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30684, d298122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30685 q = 1) (hb : d261985 q = 1) : d298123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d298123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30685, d298123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30851 q = 1) (hb : d261985 q = 1) : d298261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30851, d298261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30851, d298261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30852 q = 1) (hb : d261985 q = 1) : d298262 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
  have h15 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30853 q = 1) (hb : d261985 q = 1) : d298263 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30854 q = 1) (hb : d261985 q = 1) : d298264 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30855 q = 1) (hb : d261985 q = 1) : d298265 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d261985 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d30856 q = 1) (hb : d261985 q = 1) : d298266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30856, d298266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d30856, d298266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d30857 q = 1) (hb : d261985 q = 1) : d298267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30857, d298267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30857, d298267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro76849 (p : Pattern) (ha : d30863 p = 1) (hb : d261985 p = 1) : d298273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d261985 q = 1) : d298268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76848 q ha hb
    | true =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d261985 q = 1) : d298269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d261985 q = 1) : d298270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d261985 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30688 q = 1) (hb : d261985 q = 1) : d298126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
    | true =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30689 q = 1) (hb : d261985 q = 1) : d298127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30690 q = 1) (hb : d261985 q = 1) : d298128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30861 q = 1) (hb : d261985 q = 1) : d298271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d261985 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30691 q = 1) (hb : d261985 q = 1) : d298129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d298129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30691, d298129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30862 q = 1) (hb : d261985 q = 1) : d298272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30862, d298272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30862, d298272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30863 q = 1) (hb : d261985 q = 1) : d298273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30863, d298273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30863, d298273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro76850 (p : Pattern) (ha : d30869 p = 1) (hb : d261985 p = 1) : d298279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30864 q = 1) (hb : d261985 q = 1) : d298274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30864, d298274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76849 q ha hb
    | true =>
      simp only [d30864, d298274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30865 q = 1) (hb : d261985 q = 1) : d298275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30865, d298275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30865, d298275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30694 q = 1) (hb : d261985 q = 1) : d298132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76825 q ha hb
    | true =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30695 q = 1) (hb : d261985 q = 1) : d298133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30866 q = 1) (hb : d261985 q = 1) : d298276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30866, d298276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30866, d298276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30867 q = 1) (hb : d261985 q = 1) : d298277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30867, d298277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30867, d298277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30868 q = 1) (hb : d261985 q = 1) : d298278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30868, d298278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30868, d298278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30869 q = 1) (hb : d261985 q = 1) : d298279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30869, d298279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30869, d298279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76851 (p : Pattern) (ha : d30894 p = 1) (hb : d261985 p = 1) : d298285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d261985 q = 1) : d298132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76825 q ha hb
    | true =>
      simp only [d30694, d298132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d261985 q = 1) : d298133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d298133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30891 q = 1) (hb : d261985 q = 1) : d298282 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30891, d298282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30891, d298282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30892 q = 1) (hb : d261985 q = 1) : d298283 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30892, d298283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30892, d298283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30893 q = 1) (hb : d261985 q = 1) : d298284 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30893, d298284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30893, d298284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30894 q = 1) (hb : d261985 q = 1) : d298285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30894, d298285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30894, d298285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76852 (p : Pattern) (ha : d245414 p = 1) (hb : d261985 p = 1) : d298291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30870 q = 1) (hb : d261985 q = 1) : d298280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30870, d298280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76850 q ha hb
    | true =>
      simp only [d30870, d298280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76826 q ha hb
  have h2 (q : Pattern) (ha : d245410 q = 1) (hb : d261985 q = 1) : d298281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d298281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245410, d298281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30895 q = 1) (hb : d261985 q = 1) : d298286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30895, d298286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76851 q ha hb
    | true =>
      simp only [d30895, d298286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30896 q = 1) (hb : d261985 q = 1) : d298287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30896, d298287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30896, d298287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d261985 q = 1) : d298288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d298288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245411, d298288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d261985 q = 1) : d298289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d298289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d298289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d261985 q = 1) : d298290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d298290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d298290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d261985 q = 1) : d298291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d298291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d298291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76853 (p : Pattern) (ha : d245420 p = 1) (hb : d261985 p = 1) : d298297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30722 q = 1) (hb : d261985 q = 1) : d298160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30722, d298160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30722, d298160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76829 q ha hb
  have h2 (q : Pattern) (ha : d30723 q = 1) (hb : d261985 q = 1) : d298161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30723, d298161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30723, d298161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30729 q = 1) (hb : d261985 q = 1) : d298167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76829 q ha hb
    | true =>
      simp only [d30729, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76830 q ha hb
  have h4 (q : Pattern) (ha : d30730 q = 1) (hb : d261985 q = 1) : d298168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30730, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30731 q = 1) (hb : d261985 q = 1) : d298169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30731, d298169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30731, d298169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245398 q = 1) (hb : d261985 q = 1) : d298243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d298243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76841 q ha hb
    | true =>
      simp only [d245398, d298243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76846 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d261985 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30835 q = 1) (hb : d261985 q = 1) : d298245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30835, d298245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76831 q ha hb
    | true =>
      simp only [d30835, d298245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245399 q = 1) (hb : d261985 q = 1) : d298246 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d298246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245399, d298246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245400 q = 1) (hb : d261985 q = 1) : d298247 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d298247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245400, d298247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d245401 q = 1) (hb : d261985 q = 1) : d298248 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d298248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245401, d298248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245405 q = 1) (hb : d261985 q = 1) : d298252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d298252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245405, d298252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76847 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d261985 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d245406 q = 1) (hb : d261985 q = 1) : d298253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d298253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245406, d298253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245407 q = 1) (hb : d261985 q = 1) : d298254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d298254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245407, d298254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245408 q = 1) (hb : d261985 q = 1) : d298255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d298255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245408, d298255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d245409 q = 1) (hb : d261985 q = 1) : d298256 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d298256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245409, d298256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d245415 q = 1) (hb : d261985 q = 1) : d298292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d298292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245415, d298292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76852 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d261985 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d245416 q = 1) (hb : d261985 q = 1) : d298293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d298293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245416, d298293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d245417 q = 1) (hb : d261985 q = 1) : d298294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d298294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245417, d298294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245418 q = 1) (hb : d261985 q = 1) : d298295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d298295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245418, d298295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245419 q = 1) (hb : d261985 q = 1) : d298296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d298296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245419, d298296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d245420 q = 1) (hb : d261985 q = 1) : d298297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d298297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245420, d298297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro76854 (p : Pattern) (ha : d245426 p = 1) (hb : d261985 p = 1) : d298303 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d261985 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245383 q = 1) (hb : d261985 q = 1) : d298150 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245383, d298150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245383, d298150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76828 q ha hb
  have h3 (q : Pattern) (ha : d245384 q = 1) (hb : d261985 q = 1) : d298151 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245384, d298151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245384, d298151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245385 q = 1) (hb : d261985 q = 1) : d298152 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245385, d298152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245385, d298152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245386 q = 1) (hb : d261985 q = 1) : d298153 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245386, d298153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245386, d298153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245387 q = 1) (hb : d261985 q = 1) : d298154 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245387, d298154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245387, d298154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245421 q = 1) (hb : d261985 q = 1) : d298298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d298298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245421, d298298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76853 q ha hb
  have h8 (q : Pattern) (ha : d245422 q = 1) (hb : d261985 q = 1) : d298299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d298299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245422, d298299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245423 q = 1) (hb : d261985 q = 1) : d298300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d298300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245423, d298300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245424 q = 1) (hb : d261985 q = 1) : d298301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d298301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245424, d298301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245425 q = 1) (hb : d261985 q = 1) : d298302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d298302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245425, d298302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245426 q = 1) (hb : d261985 q = 1) : d298303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d298303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245426, d298303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro76855 (p : Pattern) (ha : d30915 p = 1) (hb : d261985 p = 1) : d298306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d261985 q = 1) : d298200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76837 q ha hb
    | true =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d261985 q = 1) : d298201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d261985 q = 1) : d298202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d261985 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30645 q = 1) (hb : d261985 q = 1) : d298083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
    | true =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30646 q = 1) (hb : d261985 q = 1) : d298084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30647 q = 1) (hb : d261985 q = 1) : d298085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30768 q = 1) (hb : d261985 q = 1) : d298203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30913 q = 1) (hb : d261985 q = 1) : d298304 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d298304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30913, d298304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30914 q = 1) (hb : d261985 q = 1) : d298305 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30914, d298305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30914, d298305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30915 q = 1) (hb : d261985 q = 1) : d298306 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30915, d298306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30915, d298306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro76856 (p : Pattern) (ha : d30919 p = 1) (hb : d261985 p = 1) : d298310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d261985 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30645 q = 1) (hb : d261985 q = 1) : d298083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
    | true =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30646 q = 1) (hb : d261985 q = 1) : d298084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30647 q = 1) (hb : d261985 q = 1) : d298085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30913 q = 1) (hb : d261985 q = 1) : d298304 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d298304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30913, d298304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30918 q = 1) (hb : d261985 q = 1) : d298309 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30918, d298309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30918, d298309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30919 q = 1) (hb : d261985 q = 1) : d298310 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30919, d298310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30919, d298310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76857 (p : Pattern) (ha : d30925 p = 1) (hb : d261985 p = 1) : d298316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d261985 q = 1) : d298314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d261985 q = 1) : d298315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d298315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d298315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30925 q = 1) (hb : d261985 q = 1) : d298316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30925, d298316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30925, d298316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76858 (p : Pattern) (ha : d30929 p = 1) (hb : d261985 p = 1) : d298320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d261985 q = 1) : d298318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d261985 q = 1) : d298319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d298319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d298319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30929 q = 1) (hb : d261985 q = 1) : d298320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30929, d298320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30929, d298320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76859 (p : Pattern) (ha : d30935 p = 1) (hb : d261985 p = 1) : d298326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d261985 q = 1) : d298321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76857 q ha hb
    | true =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76858 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d261985 q = 1) : d298322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d261985 q = 1) : d298323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d261985 q = 1) : d298324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d261985 q = 1) : d298325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30935 q = 1) (hb : d261985 q = 1) : d298326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30935, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30935, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76860 (p : Pattern) (ha : d30938 p = 1) (hb : d261985 p = 1) : d298329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d261985 q = 1) : d298314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d261985 q = 1) : d298315 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d298315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d298315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30938 q = 1) (hb : d261985 q = 1) : d298329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30938, d298329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30938, d298329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76861 (p : Pattern) (ha : d30939 p = 1) (hb : d261985 p = 1) : d298330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d261985 q = 1) : d298318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d261985 q = 1) : d298319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d298319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d298319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30939 q = 1) (hb : d261985 q = 1) : d298330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30939, d298330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30939, d298330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76862 (p : Pattern) (ha : d30945 p = 1) (hb : d261985 p = 1) : d298336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d261985 q = 1) : d298321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76857 q ha hb
    | true =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76858 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d261985 q = 1) : d298322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d261985 q = 1) : d298323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d261985 q = 1) : d298324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d261985 q = 1) : d298325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30940 q = 1) (hb : d261985 q = 1) : d298331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76860 q ha hb
    | true =>
      simp only [d30940, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76861 q ha hb
  have h7 (q : Pattern) (ha : d30941 q = 1) (hb : d261985 q = 1) : d298332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30942 q = 1) (hb : d261985 q = 1) : d298333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30942, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30943 q = 1) (hb : d261985 q = 1) : d298334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30944 q = 1) (hb : d261985 q = 1) : d298335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30945 q = 1) (hb : d261985 q = 1) : d298336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30945, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30945, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76863 (p : Pattern) (ha : d31097 p = 1) (hb : d261985 p = 1) : d298435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d261985 q = 1) : d298321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76857 q ha hb
    | true =>
      simp only [d30930, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76858 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d261985 q = 1) : d298322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d261985 q = 1) : d298323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d261985 q = 1) : d298324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d261985 q = 1) : d298325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31092 q = 1) (hb : d261985 q = 1) : d298430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d298430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76858 q ha hb
    | true =>
      simp only [d31092, d298430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31093 q = 1) (hb : d261985 q = 1) : d298431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d298431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d298431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31094 q = 1) (hb : d261985 q = 1) : d298432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d298432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31094, d298432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31095 q = 1) (hb : d261985 q = 1) : d298433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d298433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d298433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31096 q = 1) (hb : d261985 q = 1) : d298434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d298434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d298434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31097 q = 1) (hb : d261985 q = 1) : d298435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31097, d298435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31097, d298435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76864 (p : Pattern) (ha : d31103 p = 1) (hb : d261985 p = 1) : d298441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31092 q = 1) (hb : d261985 q = 1) : d298430 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d298430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76858 q ha hb
    | true =>
      simp only [d31092, d298430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31093 q = 1) (hb : d261985 q = 1) : d298431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d298431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d298431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31094 q = 1) (hb : d261985 q = 1) : d298432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d298432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31094, d298432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31095 q = 1) (hb : d261985 q = 1) : d298433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d298433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d298433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31096 q = 1) (hb : d261985 q = 1) : d298434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d298434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d298434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31098 q = 1) (hb : d261985 q = 1) : d298436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d298436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76861 q ha hb
    | true =>
      simp only [d31098, d298436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31099 q = 1) (hb : d261985 q = 1) : d298437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d298437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d298437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31100 q = 1) (hb : d261985 q = 1) : d298438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d298438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31100, d298438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31101 q = 1) (hb : d261985 q = 1) : d298439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d298439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d298439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31102 q = 1) (hb : d261985 q = 1) : d298440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d298440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d298440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31103 q = 1) (hb : d261985 q = 1) : d298441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31103, d298441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31103, d298441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76865 (p : Pattern) (ha : d31112 p = 1) (hb : d261985 p = 1) : d298450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31098 q = 1) (hb : d261985 q = 1) : d298436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d298436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76861 q ha hb
    | true =>
      simp only [d31098, d298436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31099 q = 1) (hb : d261985 q = 1) : d298437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d298437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d298437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31100 q = 1) (hb : d261985 q = 1) : d298438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d298438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31100, d298438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31101 q = 1) (hb : d261985 q = 1) : d298439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d298439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d298439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31102 q = 1) (hb : d261985 q = 1) : d298440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d298440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d298440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31112 q = 1) (hb : d261985 q = 1) : d298450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31112, d298450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31112, d298450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76866 (p : Pattern) (ha : d31155 p = 1) (hb : d261985 p = 1) : d298493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d261985 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30688 q = 1) (hb : d261985 q = 1) : d298126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
    | true =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30689 q = 1) (hb : d261985 q = 1) : d298127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30690 q = 1) (hb : d261985 q = 1) : d298128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31145 q = 1) (hb : d261985 q = 1) : d298483 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d298483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31145, d298483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31154 q = 1) (hb : d261985 q = 1) : d298492 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31154, d298492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31154, d298492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31155 q = 1) (hb : d261985 q = 1) : d298493 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31155, d298493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31155, d298493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro76867 (p : Pattern) (ha : d31211 p = 1) (hb : d261985 p = 1) : d298516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31156 q = 1) (hb : d261985 q = 1) : d298494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d298494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76866 q ha hb
    | true =>
      simp only [d31156, d298494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31157 q = 1) (hb : d261985 q = 1) : d298495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d298495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d298495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31208 q = 1) (hb : d261985 q = 1) : d298513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31208, d298513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31208, d298513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31209 q = 1) (hb : d261985 q = 1) : d298514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31209, d298514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31209, d298514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31210 q = 1) (hb : d261985 q = 1) : d298515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31210, d298515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31210, d298515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31211 q = 1) (hb : d261985 q = 1) : d298516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31211, d298516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31211, d298516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76868 (p : Pattern) (ha : d31217 p = 1) (hb : d261985 p = 1) : d298522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31212 q = 1) (hb : d261985 q = 1) : d298517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31212, d298517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76867 q ha hb
    | true =>
      simp only [d31212, d298517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31213 q = 1) (hb : d261985 q = 1) : d298518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31213, d298518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31213, d298518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31214 q = 1) (hb : d261985 q = 1) : d298519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31214, d298519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31214, d298519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31215 q = 1) (hb : d261985 q = 1) : d298520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31215, d298520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31215, d298520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31216 q = 1) (hb : d261985 q = 1) : d298521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31216, d298521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31216, d298521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31217 q = 1) (hb : d261985 q = 1) : d298522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31217, d298522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31217, d298522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76869 (p : Pattern) (ha : d30950 p = 1) (hb : d261985 p = 1) : d298341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d261985 q = 1) : d298314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d261985 q = 1) : d298340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d298340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d298340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30950 q = 1) (hb : d261985 q = 1) : d298341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30950, d298341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30950, d298341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76870 (p : Pattern) (ha : d30952 p = 1) (hb : d261985 p = 1) : d298343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d261985 q = 1) : d298318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d261985 q = 1) : d298342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d298342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d298342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30952 q = 1) (hb : d261985 q = 1) : d298343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30952, d298343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30952, d298343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76871 (p : Pattern) (ha : d30959 p = 1) (hb : d261985 p = 1) : d298350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d261985 q = 1) : d298348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d298348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d298348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d261985 q = 1) : d298349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d298349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d298349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30959 q = 1) (hb : d261985 q = 1) : d298350 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30959, d298350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30959, d298350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76872 (p : Pattern) (ha : d30962 p = 1) (hb : d261985 p = 1) : d298353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d261985 q = 1) : d298351 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d298351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d298351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d261985 q = 1) : d298352 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d298352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d298352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30962 q = 1) (hb : d261985 q = 1) : d298353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30962, d298353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30962, d298353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76873 (p : Pattern) (ha : d30966 p = 1) (hb : d261985 p = 1) : d264334 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d528 q = 1) : d528 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d529 q = 1) (hb : d261984 q = 1) : d33553 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d529, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30966 q = 1) (hb : d261985 q = 1) : d264334 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30966, d261985, d264334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30966, d261985, d264334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro76874 (p : Pattern) (ha : d30970 p = 1) (hb : d261985 p = 1) : d264156 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d310 q = 1) : d310 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d535 q = 1) (hb : d261984 q = 1) : d33326 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d535, d261984, d33326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30970 q = 1) (hb : d261985 q = 1) : d264156 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30970, d261985, d264156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30970, d261985, d264156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro76875 (p : Pattern) (ha : d30976 p = 1) (hb : d261985 p = 1) : d298360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30971 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76874 q ha hb
    | true =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30972 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30973 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30974 q = 1) (hb : d261985 q = 1) : d298358 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30974, d298358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30974, d298358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30975 q = 1) (hb : d261985 q = 1) : d298359 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30975, d298359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30975, d298359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30748 q = 1) (hb : d261985 q = 1) : d298183 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30749 q = 1) (hb : d261985 q = 1) : d298184 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30976 q = 1) (hb : d261985 q = 1) : d298360 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30976, d298360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30976, d298360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76876 (p : Pattern) (ha : d30981 p = 1) (hb : d261985 p = 1) : d298365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30748 q = 1) (hb : d261985 q = 1) : d298183 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30748, d298183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30749 q = 1) (hb : d261985 q = 1) : d298184 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30749, d298184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30756 q = 1) (hb : d261985 q = 1) : d298191 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30757 q = 1) (hb : d261985 q = 1) : d298192 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30981 q = 1) (hb : d261985 q = 1) : d298365 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30981, d298365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30981, d298365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro76877 (p : Pattern) (ha : d30989 p = 1) (hb : d261985 p = 1) : d298373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30987 q = 1) (hb : d261985 q = 1) : d298371 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30988 q = 1) (hb : d261985 q = 1) : d298372 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30756 q = 1) (hb : d261985 q = 1) : d298191 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30756, d298191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30757 q = 1) (hb : d261985 q = 1) : d298192 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30757, d298192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30989 q = 1) (hb : d261985 q = 1) : d298373 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30989, d298373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30989, d298373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro76878 (p : Pattern) (ha : d30995 p = 1) (hb : d261985 p = 1) : d298379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d261985 q = 1) : d298361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
    | true =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d261985 q = 1) : d298362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d261985 q = 1) : d298363 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d298363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d298363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d261985 q = 1) : d298364 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d298364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d298364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d261985 q = 1) : d298366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
    | true =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d261985 q = 1) : d298367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d261985 q = 1) : d298368 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d298368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d298368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d261985 q = 1) : d298369 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d298369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d298369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d261985 q = 1) : d298370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d298370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d298370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30992 q = 1) (hb : d261985 q = 1) : d298376 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30993 q = 1) (hb : d261985 q = 1) : d298377 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30761 q = 1) (hb : d261985 q = 1) : d298196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30762 q = 1) (hb : d261985 q = 1) : d298197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30994 q = 1) (hb : d261985 q = 1) : d298378 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30994, d298378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30994, d298378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30995 q = 1) (hb : d261985 q = 1) : d298379 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30995, d298379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30995, d298379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76879 (p : Pattern) (ha : d30999 p = 1) (hb : d261985 p = 1) : d298383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30761 q = 1) (hb : d261985 q = 1) : d298196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d298196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30762 q = 1) (hb : d261985 q = 1) : d298197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30762, d298197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d261985 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30763 q = 1) (hb : d261985 q = 1) : d298198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30763, d298198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30763, d298198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d261985 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30999 q = 1) (hb : d261985 q = 1) : d298383 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30999, d298383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30999, d298383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76880 (p : Pattern) (ha : d31005 p = 1) (hb : d261985 p = 1) : d298389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30996 q = 1) (hb : d261985 q = 1) : d298380 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30996, d298380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76878 q ha hb
    | true =>
      simp only [d30996, d298380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76837 q ha hb
  have h2 (q : Pattern) (ha : d30997 q = 1) (hb : d261985 q = 1) : d298381 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30997, d298381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30997, d298381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30998 q = 1) (hb : d261985 q = 1) : d298382 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30998, d298382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30998, d298382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31000 q = 1) (hb : d261985 q = 1) : d298384 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31000, d298384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76837 q ha hb
    | true =>
      simp only [d31000, d298384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76879 q ha hb
  have h5 (q : Pattern) (ha : d31001 q = 1) (hb : d261985 q = 1) : d298385 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31001, d298385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31001, d298385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31002 q = 1) (hb : d261985 q = 1) : d298386 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31002, d298386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31002, d298386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31003 q = 1) (hb : d261985 q = 1) : d298387 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31003, d298387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31003, d298387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30765 q = 1) (hb : d261985 q = 1) : d298200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76837 q ha hb
    | true =>
      simp only [d30765, d298200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
  have h9 (q : Pattern) (ha : d30766 q = 1) (hb : d261985 q = 1) : d298201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d298201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30767 q = 1) (hb : d261985 q = 1) : d298202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d298202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d261985 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30645 q = 1) (hb : d261985 q = 1) : d298083 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76817 q ha hb
    | true =>
      simp only [d30645, d298083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30646 q = 1) (hb : d261985 q = 1) : d298084 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d298084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30647 q = 1) (hb : d261985 q = 1) : d298085 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d298085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30768 q = 1) (hb : d261985 q = 1) : d298203 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30768, d298203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31004 q = 1) (hb : d261985 q = 1) : d298388 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31004, d298388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31004, d298388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31005 q = 1) (hb : d261985 q = 1) : d298389 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31005, d298389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31005, d298389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro76881 (p : Pattern) (ha : d31011 p = 1) (hb : d261985 p = 1) : d298395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d261985 q = 1) : d298390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d298390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76880 q ha hb
    | true =>
      simp only [d31006, d298390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d261985 q = 1) : d298391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d298391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d298391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d261985 q = 1) : d298392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d298392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d298392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d261985 q = 1) : d298393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d298393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d298393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d261985 q = 1) : d298394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d298394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d298394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31011 q = 1) (hb : d261985 q = 1) : d298395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31011, d298395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31011, d298395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76882 (p : Pattern) (ha : d31060 p = 1) (hb : d261985 p = 1) : d298401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d261985 q = 1) : d298398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d298398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d298398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d261985 q = 1) : d298399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d298399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d298399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d261985 q = 1) : d298400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d298400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d298400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31060 q = 1) (hb : d261985 q = 1) : d298401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31060, d298401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31060, d298401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76883 (p : Pattern) (ha : d245431 p = 1) (hb : d261985 p = 1) : d298407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d261985 q = 1) : d298344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d298344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76869 q ha hb
    | true =>
      simp only [d30953, d298344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76870 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d261985 q = 1) : d298345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d298345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d298345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d261985 q = 1) : d298346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d298346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d298346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d261985 q = 1) : d298347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d298347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d298347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d261985 q = 1) : d298354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d298354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76871 q ha hb
    | true =>
      simp only [d30963, d298354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76872 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d261985 q = 1) : d298355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d298355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d298355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d261985 q = 1) : d298356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d298356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d298356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d261985 q = 1) : d298396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d298396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76881 q ha hb
    | true =>
      simp only [d31012, d298396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76857 q ha hb
  have h9 (q : Pattern) (ha : d245427 q = 1) (hb : d261985 q = 1) : d298397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d298397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245427, d298397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d261985 q = 1) : d298402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d298402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76882 q ha hb
    | true =>
      simp only [d31061, d298402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d261985 q = 1) : d298403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d298403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d298403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245428 q = 1) (hb : d261985 q = 1) : d298404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d298404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d298404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245429 q = 1) (hb : d261985 q = 1) : d298405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d298405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245429, d298405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245430 q = 1) (hb : d261985 q = 1) : d298406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d298406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245430, d298406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245431 q = 1) (hb : d261985 q = 1) : d298407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d298407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245431, d298407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76884 (p : Pattern) (ha : d31067 p = 1) (hb : d261985 p = 1) : d298408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d261985 q = 1) : d298314 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d298314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d261985 q = 1) : d298340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d298340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d298340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31067 q = 1) (hb : d261985 q = 1) : d298408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31067, d298408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31067, d298408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76885 (p : Pattern) (ha : d31068 p = 1) (hb : d261985 p = 1) : d298409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d261985 q = 1) : d298318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d298318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d261985 q = 1) : d298342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d298342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d298342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31068 q = 1) (hb : d261985 q = 1) : d298409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31068, d298409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31068, d298409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76886 (p : Pattern) (ha : d31073 p = 1) (hb : d261985 p = 1) : d298414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d261985 q = 1) : d298313 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d298313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d261985 q = 1) : d298348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d298348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d298348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d261985 q = 1) : d298349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d298349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d298349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31073 q = 1) (hb : d261985 q = 1) : d298414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31073, d298414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31073, d298414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76887 (p : Pattern) (ha : d31074 p = 1) (hb : d261985 p = 1) : d298415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d261985 q = 1) : d298311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76856 q ha hb
    | true =>
      simp only [d30920, d298311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d261985 q = 1) : d298312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d298312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d261985 q = 1) : d298317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d298317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d261985 q = 1) : d298351 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d298351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d298351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d261985 q = 1) : d298352 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d298352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d298352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31074 q = 1) (hb : d261985 q = 1) : d298415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31074, d298415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31074, d298415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76888 (p : Pattern) (ha : d31078 p = 1) (hb : d261985 p = 1) : d298419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d261985 q = 1) : d298390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d298390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76880 q ha hb
    | true =>
      simp only [d31006, d298390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d261985 q = 1) : d298391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d298391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d298391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d261985 q = 1) : d298392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d298392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d298392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d261985 q = 1) : d298393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d298393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d298393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d261985 q = 1) : d298394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d298394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d298394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31078 q = 1) (hb : d261985 q = 1) : d298419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31078, d298419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31078, d298419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76889 (p : Pattern) (ha : d31084 p = 1) (hb : d261985 p = 1) : d298422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d261985 q = 1) : d298307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76855 q ha hb
    | true =>
      simp only [d30916, d298307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d261985 q = 1) : d298308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d298308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d261985 q = 1) : d298398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d298398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d298398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d261985 q = 1) : d298399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d298399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d298399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d261985 q = 1) : d298400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d298400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d298400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31084 q = 1) (hb : d261985 q = 1) : d298422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31084, d298422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31084, d298422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76890 (p : Pattern) (ha : d245436 p = 1) (hb : d261985 p = 1) : d298428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d261985 q = 1) : d298344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d298344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76869 q ha hb
    | true =>
      simp only [d30953, d298344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76870 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d261985 q = 1) : d298345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d298345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d298345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d261985 q = 1) : d298346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d298346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d298346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d261985 q = 1) : d298347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d298347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d298347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d261985 q = 1) : d298354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d298354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76871 q ha hb
    | true =>
      simp only [d30963, d298354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76872 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d261985 q = 1) : d298355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d298355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d298355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d261985 q = 1) : d298356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d298356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d298356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d261985 q = 1) : d298396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d298396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76881 q ha hb
    | true =>
      simp only [d31012, d298396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76857 q ha hb
  have h9 (q : Pattern) (ha : d245427 q = 1) (hb : d261985 q = 1) : d298397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d298397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245427, d298397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d261985 q = 1) : d298402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d298402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76882 q ha hb
    | true =>
      simp only [d31061, d298402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d261985 q = 1) : d298403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d298403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d298403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245428 q = 1) (hb : d261985 q = 1) : d298404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d298404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d298404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245429 q = 1) (hb : d261985 q = 1) : d298405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d298405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245429, d298405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245430 q = 1) (hb : d261985 q = 1) : d298406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d298406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245430, d298406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31069 q = 1) (hb : d261985 q = 1) : d298410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31069, d298410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76884 q ha hb
    | true =>
      simp only [d31069, d298410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76885 q ha hb
  have h16 (q : Pattern) (ha : d31070 q = 1) (hb : d261985 q = 1) : d298411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31070, d298411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31070, d298411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31071 q = 1) (hb : d261985 q = 1) : d298412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31071, d298412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31071, d298412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31072 q = 1) (hb : d261985 q = 1) : d298413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31072, d298413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31072, d298413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31075 q = 1) (hb : d261985 q = 1) : d298416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31075, d298416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76886 q ha hb
    | true =>
      simp only [d31075, d298416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76887 q ha hb
  have h20 (q : Pattern) (ha : d31076 q = 1) (hb : d261985 q = 1) : d298417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31076, d298417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31076, d298417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31077 q = 1) (hb : d261985 q = 1) : d298418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31077, d298418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31077, d298418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31079 q = 1) (hb : d261985 q = 1) : d298420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d298420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76888 q ha hb
    | true =>
      simp only [d31079, d298420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76860 q ha hb
  have h23 (q : Pattern) (ha : d245432 q = 1) (hb : d261985 q = 1) : d298421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d298421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245432, d298421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31085 q = 1) (hb : d261985 q = 1) : d298423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d298423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76889 q ha hb
    | true =>
      simp only [d31085, d298423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31086 q = 1) (hb : d261985 q = 1) : d298424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d298424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31086, d298424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245433 q = 1) (hb : d261985 q = 1) : d298425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d298425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245433, d298425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245434 q = 1) (hb : d261985 q = 1) : d298426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d298426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245434, d298426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245435 q = 1) (hb : d261985 q = 1) : d298427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d298427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245435, d298427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245436 q = 1) (hb : d261985 q = 1) : d298428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d298428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245436, d298428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro76891 (p : Pattern) (ha : d245443 p = 1) (hb : d261985 p = 1) : d298448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31079 q = 1) (hb : d261985 q = 1) : d298420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d298420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76888 q ha hb
    | true =>
      simp only [d31079, d298420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76860 q ha hb
  have h2 (q : Pattern) (ha : d245432 q = 1) (hb : d261985 q = 1) : d298421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d298421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245432, d298421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31085 q = 1) (hb : d261985 q = 1) : d298423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d298423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76889 q ha hb
    | true =>
      simp only [d31085, d298423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31086 q = 1) (hb : d261985 q = 1) : d298424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d298424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31086, d298424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245433 q = 1) (hb : d261985 q = 1) : d298425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d298425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245433, d298425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245441 q = 1) (hb : d261985 q = 1) : d298446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d298446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245441, d298446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245442 q = 1) (hb : d261985 q = 1) : d298447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d298447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245442, d298447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d261985 q = 1) : d298448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d298448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d298448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76892 (p : Pattern) (ha : d31132 p = 1) (hb : d261985 p = 1) : d298470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31118 q = 1) (hb : d261985 q = 1) : d298456 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31118, d298456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31118, d298456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
  have h2 (q : Pattern) (ha : d30977 q = 1) (hb : d261985 q = 1) : d298361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
    | true =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31119 q = 1) (hb : d261985 q = 1) : d298457 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31119, d298457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31119, d298457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30978 q = 1) (hb : d261985 q = 1) : d298362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31120 q = 1) (hb : d261985 q = 1) : d298458 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31120, d298458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31120, d298458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31121 q = 1) (hb : d261985 q = 1) : d298459 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31121, d298459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31121, d298459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31122 q = 1) (hb : d261985 q = 1) : d298460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31122, d298460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31122, d298460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
  have h8 (q : Pattern) (ha : d30982 q = 1) (hb : d261985 q = 1) : d298366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
    | true =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31123 q = 1) (hb : d261985 q = 1) : d298461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31123, d298461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31123, d298461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30983 q = 1) (hb : d261985 q = 1) : d298367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31124 q = 1) (hb : d261985 q = 1) : d298462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31124, d298462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31124, d298462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31125 q = 1) (hb : d261985 q = 1) : d298463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31125, d298463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31125, d298463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31126 q = 1) (hb : d261985 q = 1) : d298464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31126, d298464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31126, d298464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31127 q = 1) (hb : d261985 q = 1) : d298465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
  have h15 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31128 q = 1) (hb : d261985 q = 1) : d298466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31129 q = 1) (hb : d261985 q = 1) : d298467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31130 q = 1) (hb : d261985 q = 1) : d298468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30852 q = 1) (hb : d261985 q = 1) : d298262 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
  have h21 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d30853 q = 1) (hb : d261985 q = 1) : d298263 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d30854 q = 1) (hb : d261985 q = 1) : d298264 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d30855 q = 1) (hb : d261985 q = 1) : d298265 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31131 q = 1) (hb : d261985 q = 1) : d298469 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31131, d298469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31131, d298469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31132 q = 1) (hb : d261985 q = 1) : d298470 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31132, d298470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31132, d298470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro76893 (p : Pattern) (ha : d31136 p = 1) (hb : d261985 p = 1) : d298474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30852 q = 1) (hb : d261985 q = 1) : d298262 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d298262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
  have h2 (q : Pattern) (ha : d30759 q = 1) (hb : d261985 q = 1) : d298194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76836 q ha hb
    | true =>
      simp only [d30759, d298194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30853 q = 1) (hb : d261985 q = 1) : d298263 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30853, d298263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30760 q = 1) (hb : d261985 q = 1) : d298195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30760, d298195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30854 q = 1) (hb : d261985 q = 1) : d298264 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30854, d298264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30855 q = 1) (hb : d261985 q = 1) : d298265 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30855, d298265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d261985 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30856 q = 1) (hb : d261985 q = 1) : d298266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30856, d298266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30856, d298266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d261985 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31136 q = 1) (hb : d261985 q = 1) : d298474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31136, d298474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31136, d298474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro76894 (p : Pattern) (ha : d31142 p = 1) (hb : d261985 p = 1) : d298480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31133 q = 1) (hb : d261985 q = 1) : d298471 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31133, d298471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76892 q ha hb
    | true =>
      simp only [d31133, d298471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76848 q ha hb
  have h2 (q : Pattern) (ha : d31134 q = 1) (hb : d261985 q = 1) : d298472 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31134, d298472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31134, d298472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31135 q = 1) (hb : d261985 q = 1) : d298473 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31135, d298473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31135, d298473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31137 q = 1) (hb : d261985 q = 1) : d298475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31137, d298475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76848 q ha hb
    | true =>
      simp only [d31137, d298475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76893 q ha hb
  have h5 (q : Pattern) (ha : d31138 q = 1) (hb : d261985 q = 1) : d298476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31138, d298476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31138, d298476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31139 q = 1) (hb : d261985 q = 1) : d298477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31139, d298477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31139, d298477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31140 q = 1) (hb : d261985 q = 1) : d298478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31140, d298478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31140, d298478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30858 q = 1) (hb : d261985 q = 1) : d298268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76848 q ha hb
    | true =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
  have h9 (q : Pattern) (ha : d30859 q = 1) (hb : d261985 q = 1) : d298269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30860 q = 1) (hb : d261985 q = 1) : d298270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d261985 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30688 q = 1) (hb : d261985 q = 1) : d298126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
    | true =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30689 q = 1) (hb : d261985 q = 1) : d298127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30690 q = 1) (hb : d261985 q = 1) : d298128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30861 q = 1) (hb : d261985 q = 1) : d298271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31141 q = 1) (hb : d261985 q = 1) : d298479 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31141, d298479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31141, d298479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31142 q = 1) (hb : d261985 q = 1) : d298480 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31142, d298480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31142, d298480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro76895 (p : Pattern) (ha : d31147 p = 1) (hb : d261985 p = 1) : d298485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d261985 q = 1) : d298268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76848 q ha hb
    | true =>
      simp only [d30858, d298268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d261985 q = 1) : d298269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d298269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d261985 q = 1) : d298270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d298270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d261985 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30688 q = 1) (hb : d261985 q = 1) : d298126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76824 q ha hb
    | true =>
      simp only [d30688, d298126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30689 q = 1) (hb : d261985 q = 1) : d298127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d298127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30690 q = 1) (hb : d261985 q = 1) : d298128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d298128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30861 q = 1) (hb : d261985 q = 1) : d298271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d298271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31145 q = 1) (hb : d261985 q = 1) : d298483 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d298483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31145, d298483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31146 q = 1) (hb : d261985 q = 1) : d298484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31146, d298484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31146, d298484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31147 q = 1) (hb : d261985 q = 1) : d298485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31147, d298485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31147, d298485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro76896 (p : Pattern) (ha : d31153 p = 1) (hb : d261985 p = 1) : d298491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31143 q = 1) (hb : d261985 q = 1) : d298481 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31143, d298481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76894 q ha hb
    | true =>
      simp only [d31143, d298481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31144 q = 1) (hb : d261985 q = 1) : d298482 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31144, d298482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31144, d298482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31148 q = 1) (hb : d261985 q = 1) : d298486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76895 q ha hb
    | true =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31149 q = 1) (hb : d261985 q = 1) : d298487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31150 q = 1) (hb : d261985 q = 1) : d298488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31150, d298488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31150, d298488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31151 q = 1) (hb : d261985 q = 1) : d298489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31151, d298489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31151, d298489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31152 q = 1) (hb : d261985 q = 1) : d298490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31152, d298490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31152, d298490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31153 q = 1) (hb : d261985 q = 1) : d298491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31153, d298491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31153, d298491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76897 (p : Pattern) (ha : d31161 p = 1) (hb : d261985 p = 1) : d298499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d261985 q = 1) : d298486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76895 q ha hb
    | true =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d261985 q = 1) : d298487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31156 q = 1) (hb : d261985 q = 1) : d298494 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d298494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76866 q ha hb
    | true =>
      simp only [d31156, d298494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31157 q = 1) (hb : d261985 q = 1) : d298495 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d298495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d298495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31158 q = 1) (hb : d261985 q = 1) : d298496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31158, d298496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31158, d298496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31159 q = 1) (hb : d261985 q = 1) : d298497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31159, d298497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31159, d298497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31160 q = 1) (hb : d261985 q = 1) : d298498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31160, d298498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31160, d298498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31161 q = 1) (hb : d261985 q = 1) : d298499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31161, d298499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31161, d298499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76898 (p : Pattern) (ha : d31200 p = 1) (hb : d261985 p = 1) : d298505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d261985 q = 1) : d298486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76895 q ha hb
    | true =>
      simp only [d31148, d298486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d261985 q = 1) : d298487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d298487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31197 q = 1) (hb : d261985 q = 1) : d298502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31197, d298502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31197, d298502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31198 q = 1) (hb : d261985 q = 1) : d298503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31198, d298503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31198, d298503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31199 q = 1) (hb : d261985 q = 1) : d298504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31199, d298504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31199, d298504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31200 q = 1) (hb : d261985 q = 1) : d298505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31200, d298505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31200, d298505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76899 (p : Pattern) (ha : d245453 p = 1) (hb : d261985 p = 1) : d298511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31162 q = 1) (hb : d261985 q = 1) : d298500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31162, d298500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76896 q ha hb
    | true =>
      simp only [d31162, d298500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76897 q ha hb
  have h2 (q : Pattern) (ha : d245449 q = 1) (hb : d261985 q = 1) : d298501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d298501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245449, d298501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31201 q = 1) (hb : d261985 q = 1) : d298506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31201, d298506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76898 q ha hb
    | true =>
      simp only [d31201, d298506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31202 q = 1) (hb : d261985 q = 1) : d298507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31202, d298507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31202, d298507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d261985 q = 1) : d298508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d298508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245450, d298508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d261985 q = 1) : d298509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d298509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d298509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d261985 q = 1) : d298510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d298510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d298510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d261985 q = 1) : d298511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d298511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d298511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76900 (p : Pattern) (ha : d245459 p = 1) (hb : d261985 p = 1) : d298528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30936 q = 1) (hb : d261985 q = 1) : d298327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30936, d298327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30936, d298327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76859 q ha hb
  have h2 (q : Pattern) (ha : d30937 q = 1) (hb : d261985 q = 1) : d298328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30937, d298328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30937, d298328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30946 q = 1) (hb : d261985 q = 1) : d298337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76859 q ha hb
    | true =>
      simp only [d30946, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76862 q ha hb
  have h4 (q : Pattern) (ha : d30947 q = 1) (hb : d261985 q = 1) : d298338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30947, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30948 q = 1) (hb : d261985 q = 1) : d298339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30948, d298339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30948, d298339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245437 q = 1) (hb : d261985 q = 1) : d298429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d298429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76883 q ha hb
    | true =>
      simp only [d245437, d298429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76890 q ha hb
  have h7 (q : Pattern) (ha : d31104 q = 1) (hb : d261985 q = 1) : d298442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31104, d298442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76863 q ha hb
    | true =>
      simp only [d31104, d298442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76864 q ha hb
  have h8 (q : Pattern) (ha : d245438 q = 1) (hb : d261985 q = 1) : d298443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d298443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245438, d298443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245439 q = 1) (hb : d261985 q = 1) : d298444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d298444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245439, d298444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245440 q = 1) (hb : d261985 q = 1) : d298445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d298445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245440, d298445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245444 q = 1) (hb : d261985 q = 1) : d298449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d298449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245444, d298449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76891 q ha hb
  have h12 (q : Pattern) (ha : d31113 q = 1) (hb : d261985 q = 1) : d298451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31113, d298451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31113, d298451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76865 q ha hb
  have h13 (q : Pattern) (ha : d245445 q = 1) (hb : d261985 q = 1) : d298452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d298452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245445, d298452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245446 q = 1) (hb : d261985 q = 1) : d298453 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d298453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245446, d298453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245447 q = 1) (hb : d261985 q = 1) : d298454 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d298454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245447, d298454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245448 q = 1) (hb : d261985 q = 1) : d298455 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d298455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245448, d298455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245454 q = 1) (hb : d261985 q = 1) : d298512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d298512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245454, d298512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76899 q ha hb
  have h18 (q : Pattern) (ha : d31218 q = 1) (hb : d261985 q = 1) : d298523 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31218, d298523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31218, d298523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76868 q ha hb
  have h19 (q : Pattern) (ha : d245455 q = 1) (hb : d261985 q = 1) : d298524 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d298524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245455, d298524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245456 q = 1) (hb : d261985 q = 1) : d298525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d298525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245456, d298525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245457 q = 1) (hb : d261985 q = 1) : d298526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d298526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245457, d298526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245458 q = 1) (hb : d261985 q = 1) : d298527 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d298527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245458, d298527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245459 q = 1) (hb : d261985 q = 1) : d298528 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d298528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245459, d298528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro76901 (p : Pattern) (ha : d245465 p = 1) (hb : d261985 p = 1) : d298534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d261985 q = 1) : d298529 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d298529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d298529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76900 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d261985 q = 1) : d298530 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d298530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d298530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d261985 q = 1) : d298531 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d298531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d298531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d261985 q = 1) : d298532 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d298532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d298532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d261985 q = 1) : d298533 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d298533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d298533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d261985 q = 1) : d298534 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d298534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d298534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76902 (p : Pattern) (ha : d31231 p = 1) (hb : d261985 p = 1) : d298536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d261985 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30636 q = 1) (hb : d261985 q = 1) : d298074 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30636, d298074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30637 q = 1) (hb : d261985 q = 1) : d298075 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30637, d298075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31231 q = 1) (hb : d261985 q = 1) : d298536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31231, d298536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31231, d298536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76903 (p : Pattern) (ha : d31237 p = 1) (hb : d261985 p = 1) : d298542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d261985 q = 1) : d298361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
    | true =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d261985 q = 1) : d298362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d261985 q = 1) : d298363 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d298363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d298363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d261985 q = 1) : d298364 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d298364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d298364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d261985 q = 1) : d298366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
    | true =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d261985 q = 1) : d298367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d261985 q = 1) : d298368 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d298368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d298368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d261985 q = 1) : d298369 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d298369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d298369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d261985 q = 1) : d298370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d298370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d298370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30992 q = 1) (hb : d261985 q = 1) : d298376 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30993 q = 1) (hb : d261985 q = 1) : d298377 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31234 q = 1) (hb : d261985 q = 1) : d298539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31235 q = 1) (hb : d261985 q = 1) : d298540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31236 q = 1) (hb : d261985 q = 1) : d298541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31236, d298541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31236, d298541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31237 q = 1) (hb : d261985 q = 1) : d298542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31237, d298542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31237, d298542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76904 (p : Pattern) (ha : d31240 p = 1) (hb : d261985 p = 1) : d298545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d261985 q = 1) : d298186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
    | true =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d261985 q = 1) : d298187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d261985 q = 1) : d298188 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d298188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d298188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d261985 q = 1) : d298189 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d298189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d298189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31234 q = 1) (hb : d261985 q = 1) : d298539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31235 q = 1) (hb : d261985 q = 1) : d298540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31238 q = 1) (hb : d261985 q = 1) : d298543 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31238, d298543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31238, d298543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31239 q = 1) (hb : d261985 q = 1) : d298544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31240 q = 1) (hb : d261985 q = 1) : d298545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31240, d298545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31240, d298545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76905 (p : Pattern) (ha : d31244 p = 1) (hb : d261985 p = 1) : d298549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31234 q = 1) (hb : d261985 q = 1) : d298539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31235 q = 1) (hb : d261985 q = 1) : d298540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31239 q = 1) (hb : d261985 q = 1) : d298544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31244 q = 1) (hb : d261985 q = 1) : d298549 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31244, d298549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31244, d298549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76906 (p : Pattern) (ha : d31251 p = 1) (hb : d261985 p = 1) : d298556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31241 q = 1) (hb : d261985 q = 1) : d298546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31241, d298546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76903 q ha hb
    | true =>
      simp only [d31241, d298546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76904 q ha hb
  have h2 (q : Pattern) (ha : d31242 q = 1) (hb : d261985 q = 1) : d298547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31242, d298547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31242, d298547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31243 q = 1) (hb : d261985 q = 1) : d298548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31243, d298548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31243, d298548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31245 q = 1) (hb : d261985 q = 1) : d298550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76904 q ha hb
    | true =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76905 q ha hb
  have h5 (q : Pattern) (ha : d31246 q = 1) (hb : d261985 q = 1) : d298551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31247 q = 1) (hb : d261985 q = 1) : d298552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31248 q = 1) (hb : d261985 q = 1) : d298553 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31248, d298553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31248, d298553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31249 q = 1) (hb : d261985 q = 1) : d298554 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d298554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31249, d298554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31250 q = 1) (hb : d261985 q = 1) : d298555 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31250, d298555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31250, d298555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31251 q = 1) (hb : d261985 q = 1) : d298556 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31251, d298556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31251, d298556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro76907 (p : Pattern) (ha : d31255 p = 1) (hb : d261985 p = 1) : d298560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31245 q = 1) (hb : d261985 q = 1) : d298550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76904 q ha hb
    | true =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76905 q ha hb
  have h2 (q : Pattern) (ha : d31246 q = 1) (hb : d261985 q = 1) : d298551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31247 q = 1) (hb : d261985 q = 1) : d298552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31249 q = 1) (hb : d261985 q = 1) : d298554 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d298554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31249, d298554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31254 q = 1) (hb : d261985 q = 1) : d298559 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31254, d298559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31254, d298559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31255 q = 1) (hb : d261985 q = 1) : d298560 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31255, d298560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31255, d298560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76908 (p : Pattern) (ha : d31261 p = 1) (hb : d261985 p = 1) : d298566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d261985 q = 1) : d298564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d261985 q = 1) : d298565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d298565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d298565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31261 q = 1) (hb : d261985 q = 1) : d298566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31261, d298566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31261, d298566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76909 (p : Pattern) (ha : d31265 p = 1) (hb : d261985 p = 1) : d298570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d261985 q = 1) : d298568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d261985 q = 1) : d298569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d298569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d298569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31265 q = 1) (hb : d261985 q = 1) : d298570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31265, d298570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31265, d298570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76910 (p : Pattern) (ha : d31271 p = 1) (hb : d261985 p = 1) : d298576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d261985 q = 1) : d298571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76908 q ha hb
    | true =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76909 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d261985 q = 1) : d298572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d261985 q = 1) : d298573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d261985 q = 1) : d298574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d261985 q = 1) : d298575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31271 q = 1) (hb : d261985 q = 1) : d298576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31271, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31271, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76911 (p : Pattern) (ha : d31274 p = 1) (hb : d261985 p = 1) : d298579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d261985 q = 1) : d298564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d261985 q = 1) : d298565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d298565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d298565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31274 q = 1) (hb : d261985 q = 1) : d298579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31274, d298579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31274, d298579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76912 (p : Pattern) (ha : d31275 p = 1) (hb : d261985 p = 1) : d298580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d261985 q = 1) : d298568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d261985 q = 1) : d298569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d298569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d298569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31275 q = 1) (hb : d261985 q = 1) : d298580 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31275, d298580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31275, d298580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76913 (p : Pattern) (ha : d31281 p = 1) (hb : d261985 p = 1) : d298586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d261985 q = 1) : d298571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76908 q ha hb
    | true =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76909 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d261985 q = 1) : d298572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d261985 q = 1) : d298573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d261985 q = 1) : d298574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d261985 q = 1) : d298575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31276 q = 1) (hb : d261985 q = 1) : d298581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76911 q ha hb
    | true =>
      simp only [d31276, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76912 q ha hb
  have h7 (q : Pattern) (ha : d31277 q = 1) (hb : d261985 q = 1) : d298582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31278 q = 1) (hb : d261985 q = 1) : d298583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31278, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31279 q = 1) (hb : d261985 q = 1) : d298584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31280 q = 1) (hb : d261985 q = 1) : d298585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31281 q = 1) (hb : d261985 q = 1) : d298586 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31281, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31281, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76914 (p : Pattern) (ha : d31454 p = 1) (hb : d261985 p = 1) : d298689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d261985 q = 1) : d298571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76908 q ha hb
    | true =>
      simp only [d31266, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76909 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d261985 q = 1) : d298572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d261985 q = 1) : d298573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d261985 q = 1) : d298574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d261985 q = 1) : d298575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31449 q = 1) (hb : d261985 q = 1) : d298684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d298684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76909 q ha hb
    | true =>
      simp only [d31449, d298684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31450 q = 1) (hb : d261985 q = 1) : d298685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d298685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d298685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31451 q = 1) (hb : d261985 q = 1) : d298686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d298686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31451, d298686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31452 q = 1) (hb : d261985 q = 1) : d298687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d298687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d298687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31453 q = 1) (hb : d261985 q = 1) : d298688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d298688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d298688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31454 q = 1) (hb : d261985 q = 1) : d298689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31454, d298689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31454, d298689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76915 (p : Pattern) (ha : d31460 p = 1) (hb : d261985 p = 1) : d298695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31449 q = 1) (hb : d261985 q = 1) : d298684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d298684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76909 q ha hb
    | true =>
      simp only [d31449, d298684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31450 q = 1) (hb : d261985 q = 1) : d298685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d298685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d298685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31451 q = 1) (hb : d261985 q = 1) : d298686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d298686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31451, d298686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31452 q = 1) (hb : d261985 q = 1) : d298687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d298687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d298687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31453 q = 1) (hb : d261985 q = 1) : d298688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d298688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d298688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31455 q = 1) (hb : d261985 q = 1) : d298690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d298690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76912 q ha hb
    | true =>
      simp only [d31455, d298690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31456 q = 1) (hb : d261985 q = 1) : d298691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d298691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d298691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31457 q = 1) (hb : d261985 q = 1) : d298692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d298692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31457, d298692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31458 q = 1) (hb : d261985 q = 1) : d298693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d298693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d298693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31459 q = 1) (hb : d261985 q = 1) : d298694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d298694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d298694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31460 q = 1) (hb : d261985 q = 1) : d298695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31460, d298695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31460, d298695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76916 (p : Pattern) (ha : d31469 p = 1) (hb : d261985 p = 1) : d298704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31455 q = 1) (hb : d261985 q = 1) : d298690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d298690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76912 q ha hb
    | true =>
      simp only [d31455, d298690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31456 q = 1) (hb : d261985 q = 1) : d298691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d298691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d298691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31457 q = 1) (hb : d261985 q = 1) : d298692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d298692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31457, d298692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31458 q = 1) (hb : d261985 q = 1) : d298693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d298693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d298693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31459 q = 1) (hb : d261985 q = 1) : d298694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d298694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d298694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31469 q = 1) (hb : d261985 q = 1) : d298704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31469, d298704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31469, d298704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76917 (p : Pattern) (ha : d31506 p = 1) (hb : d261985 p = 1) : d298741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d261985 q = 1) : d298257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d298257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d298257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d261985 q = 1) : d298186 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76835 q ha hb
    | true =>
      simp only [d30751, d298186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d261985 q = 1) : d298258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d298258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d298258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d261985 q = 1) : d298187 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d298187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d261985 q = 1) : d298259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d298259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d298259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d261985 q = 1) : d298260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d298260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d298260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31490 q = 1) (hb : d261985 q = 1) : d298725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
  have h8 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31491 q = 1) (hb : d261985 q = 1) : d298726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31492 q = 1) (hb : d261985 q = 1) : d298727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31493 q = 1) (hb : d261985 q = 1) : d298728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31505 q = 1) (hb : d261985 q = 1) : d298740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31505, d298740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31505, d298740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31499 q = 1) (hb : d261985 q = 1) : d298734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31506 q = 1) (hb : d261985 q = 1) : d298741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31506, d298741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31506, d298741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76918 (p : Pattern) (ha : d31510 p = 1) (hb : d261985 p = 1) : d298745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31490 q = 1) (hb : d261985 q = 1) : d298725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
  have h2 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31491 q = 1) (hb : d261985 q = 1) : d298726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31492 q = 1) (hb : d261985 q = 1) : d298727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31493 q = 1) (hb : d261985 q = 1) : d298728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31499 q = 1) (hb : d261985 q = 1) : d298734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31510 q = 1) (hb : d261985 q = 1) : d298745 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31510, d298745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31510, d298745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76919 (p : Pattern) (ha : d31529 p = 1) (hb : d261985 p = 1) : d298764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31511 q = 1) (hb : d261985 q = 1) : d298746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76917 q ha hb
    | true =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76918 q ha hb
  have h2 (q : Pattern) (ha : d31512 q = 1) (hb : d261985 q = 1) : d298747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31513 q = 1) (hb : d261985 q = 1) : d298748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31519 q = 1) (hb : d261985 q = 1) : d298754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31519, d298754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31519, d298754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31528 q = 1) (hb : d261985 q = 1) : d298763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31528, d298763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31528, d298763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31529 q = 1) (hb : d261985 q = 1) : d298764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31529, d298764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31529, d298764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76920 (p : Pattern) (ha : d31600 p = 1) (hb : d261985 p = 1) : d298787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31530 q = 1) (hb : d261985 q = 1) : d298765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31530, d298765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76919 q ha hb
    | true =>
      simp only [d31530, d298765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31531 q = 1) (hb : d261985 q = 1) : d298766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31531, d298766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31531, d298766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31597 q = 1) (hb : d261985 q = 1) : d298784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31597, d298784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31597, d298784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31598 q = 1) (hb : d261985 q = 1) : d298785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31598, d298785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31598, d298785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31599 q = 1) (hb : d261985 q = 1) : d298786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31599, d298786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31599, d298786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31600 q = 1) (hb : d261985 q = 1) : d298787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31600, d298787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31600, d298787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76921 (p : Pattern) (ha : d31606 p = 1) (hb : d261985 p = 1) : d298793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31601 q = 1) (hb : d261985 q = 1) : d298788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31601, d298788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76920 q ha hb
    | true =>
      simp only [d31601, d298788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31602 q = 1) (hb : d261985 q = 1) : d298789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31602, d298789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31602, d298789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31603 q = 1) (hb : d261985 q = 1) : d298790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31603, d298790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31603, d298790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31604 q = 1) (hb : d261985 q = 1) : d298791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31604, d298791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31604, d298791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31605 q = 1) (hb : d261985 q = 1) : d298792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31605, d298792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31605, d298792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31606 q = 1) (hb : d261985 q = 1) : d298793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31606, d298793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31606, d298793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76922 (p : Pattern) (ha : d31286 p = 1) (hb : d261985 p = 1) : d298591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d261985 q = 1) : d298564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31285 q = 1) (hb : d261985 q = 1) : d298590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31285, d298590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31285, d298590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31286 q = 1) (hb : d261985 q = 1) : d298591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31286, d298591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31286, d298591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76923 (p : Pattern) (ha : d31288 p = 1) (hb : d261985 p = 1) : d298593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d261985 q = 1) : d298568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31287 q = 1) (hb : d261985 q = 1) : d298592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31287, d298592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31287, d298592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31288 q = 1) (hb : d261985 q = 1) : d298593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31288, d298593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31288, d298593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76924 (p : Pattern) (ha : d31295 p = 1) (hb : d261985 p = 1) : d298600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31293 q = 1) (hb : d261985 q = 1) : d298598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31293, d298598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31293, d298598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31294 q = 1) (hb : d261985 q = 1) : d298599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31294, d298599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31294, d298599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31295 q = 1) (hb : d261985 q = 1) : d298600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31295, d298600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31295, d298600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76925 (p : Pattern) (ha : d31298 p = 1) (hb : d261985 p = 1) : d298603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31296 q = 1) (hb : d261985 q = 1) : d298601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31296, d298601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31296, d298601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31297 q = 1) (hb : d261985 q = 1) : d298602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31297, d298602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31297, d298602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31298 q = 1) (hb : d261985 q = 1) : d298603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31298, d298603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31298, d298603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76926 (p : Pattern) (ha : d28879 p = 1) (hb : d261985 p = 1) : d264334 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d528 q = 1) : d528 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d826 q = 1) (hb : d261984 q = 1) : d33553 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d826, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d826, d261984, d33553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28879 q = 1) (hb : d261985 q = 1) : d264334 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28879, d261985, d264334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28879, d261985, d264334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro76927 (p : Pattern) (ha : d31302 p = 1) (hb : d261985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d820 q = 1) (hb : d261984 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, d261984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d820, d261984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31302 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d31302, d261985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31302, d261985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro76928 (p : Pattern) (ha : d31312 p = 1) (hb : d261985 p = 1) : d298614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76927 q ha hb
    | true =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31304 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31305 q = 1) (hb : d261985 q = 1) : d298607 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28880 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76926 q ha hb
    | true =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28881 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25765 q = 1) (hb : d261985 q = 1) : d264590 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66078 q ha hb
    | true =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25766 q = 1) (hb : d261985 q = 1) : d264591 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31306 q = 1) (hb : d261985 q = 1) : d298608 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31307 q = 1) (hb : d261985 q = 1) : d298609 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31308 q = 1) (hb : d261985 q = 1) : d298610 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31309 q = 1) (hb : d261985 q = 1) : d298611 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31309, d298611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31309, d298611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31310 q = 1) (hb : d261985 q = 1) : d298612 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31310, d298612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31310, d298612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31311 q = 1) (hb : d261985 q = 1) : d298613 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31311, d298613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31311, d298613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d31312 q = 1) (hb : d261985 q = 1) : d298614 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31312, d298614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31312, d298614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro76929 (p : Pattern) (ha : d31317 p = 1) (hb : d261985 p = 1) : d298619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30971 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76874 q ha hb
    | true =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30972 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30973 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30974 q = 1) (hb : d261985 q = 1) : d298358 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30974, d298358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30974, d298358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30975 q = 1) (hb : d261985 q = 1) : d298359 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30975, d298359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30975, d298359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d30987 q = 1) (hb : d261985 q = 1) : d298371 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30988 q = 1) (hb : d261985 q = 1) : d298372 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31317 q = 1) (hb : d261985 q = 1) : d298619 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31317, d298619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31317, d298619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro76930 (p : Pattern) (ha : d31325 p = 1) (hb : d261985 p = 1) : d298627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31323 q = 1) (hb : d261985 q = 1) : d298625 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31324 q = 1) (hb : d261985 q = 1) : d298626 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30747 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30747, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30987 q = 1) (hb : d261985 q = 1) : d298371 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30987, d298371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30988 q = 1) (hb : d261985 q = 1) : d298372 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30988, d298372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31325 q = 1) (hb : d261985 q = 1) : d298627 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31325, d298627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31325, d298627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro76931 (p : Pattern) (ha : d31331 p = 1) (hb : d261985 p = 1) : d298633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31313 q = 1) (hb : d261985 q = 1) : d298615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31313, d298615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76928 q ha hb
    | true =>
      simp only [d31313, d298615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31314 q = 1) (hb : d261985 q = 1) : d298616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31314, d298616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31314, d298616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31315 q = 1) (hb : d261985 q = 1) : d298617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31315, d298617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31315, d298617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31316 q = 1) (hb : d261985 q = 1) : d298618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31316, d298618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31316, d298618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31318 q = 1) (hb : d261985 q = 1) : d298620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31318, d298620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76929 q ha hb
    | true =>
      simp only [d31318, d298620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31319 q = 1) (hb : d261985 q = 1) : d298621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31319, d298621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31319, d298621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31320 q = 1) (hb : d261985 q = 1) : d298622 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31320, d298622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31320, d298622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31321 q = 1) (hb : d261985 q = 1) : d298623 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31321, d298623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31321, d298623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31322 q = 1) (hb : d261985 q = 1) : d298624 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31322, d298624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31322, d298624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31326 q = 1) (hb : d261985 q = 1) : d298628 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31326, d298628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76930 q ha hb
    | true =>
      simp only [d31326, d298628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31327 q = 1) (hb : d261985 q = 1) : d298629 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31327, d298629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31327, d298629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31328 q = 1) (hb : d261985 q = 1) : d298630 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31328, d298630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31328, d298630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31329 q = 1) (hb : d261985 q = 1) : d298631 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31329, d298631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31329, d298631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30992 q = 1) (hb : d261985 q = 1) : d298376 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30993 q = 1) (hb : d261985 q = 1) : d298377 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31330 q = 1) (hb : d261985 q = 1) : d298632 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31330, d298632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31330, d298632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31331 q = 1) (hb : d261985 q = 1) : d298633 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31331, d298633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31331, d298633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76932 (p : Pattern) (ha : d31335 p = 1) (hb : d261985 p = 1) : d298637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30992 q = 1) (hb : d261985 q = 1) : d298376 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d298376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30993 q = 1) (hb : d261985 q = 1) : d298377 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30993, d298377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31234 q = 1) (hb : d261985 q = 1) : d298539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d298539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31235 q = 1) (hb : d261985 q = 1) : d298540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31235, d298540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31236 q = 1) (hb : d261985 q = 1) : d298541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31236, d298541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31236, d298541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31239 q = 1) (hb : d261985 q = 1) : d298544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31239, d298544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31335 q = 1) (hb : d261985 q = 1) : d298637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31335, d298637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31335, d298637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76933 (p : Pattern) (ha : d31341 p = 1) (hb : d261985 p = 1) : d298643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31332 q = 1) (hb : d261985 q = 1) : d298634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31332, d298634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76931 q ha hb
    | true =>
      simp only [d31332, d298634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76903 q ha hb
  have h2 (q : Pattern) (ha : d31333 q = 1) (hb : d261985 q = 1) : d298635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31333, d298635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31333, d298635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31334 q = 1) (hb : d261985 q = 1) : d298636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31334, d298636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31334, d298636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31336 q = 1) (hb : d261985 q = 1) : d298638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31336, d298638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76903 q ha hb
    | true =>
      simp only [d31336, d298638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76932 q ha hb
  have h5 (q : Pattern) (ha : d31337 q = 1) (hb : d261985 q = 1) : d298639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31337, d298639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31337, d298639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31338 q = 1) (hb : d261985 q = 1) : d298640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31338, d298640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31338, d298640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31339 q = 1) (hb : d261985 q = 1) : d298641 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31339, d298641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31339, d298641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31241 q = 1) (hb : d261985 q = 1) : d298546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31241, d298546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76903 q ha hb
    | true =>
      simp only [d31241, d298546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76904 q ha hb
  have h9 (q : Pattern) (ha : d31242 q = 1) (hb : d261985 q = 1) : d298547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31242, d298547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31242, d298547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31243 q = 1) (hb : d261985 q = 1) : d298548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31243, d298548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31243, d298548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31245 q = 1) (hb : d261985 q = 1) : d298550 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76904 q ha hb
    | true =>
      simp only [d31245, d298550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76905 q ha hb
  have h12 (q : Pattern) (ha : d31246 q = 1) (hb : d261985 q = 1) : d298551 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d298551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31247 q = 1) (hb : d261985 q = 1) : d298552 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d298552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31248 q = 1) (hb : d261985 q = 1) : d298553 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31248, d298553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31248, d298553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31340 q = 1) (hb : d261985 q = 1) : d298642 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31340, d298642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31340, d298642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31341 q = 1) (hb : d261985 q = 1) : d298643 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31341, d298643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31341, d298643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro76934 (p : Pattern) (ha : d31347 p = 1) (hb : d261985 p = 1) : d298649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31342 q = 1) (hb : d261985 q = 1) : d298644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31342, d298644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76933 q ha hb
    | true =>
      simp only [d31342, d298644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31343 q = 1) (hb : d261985 q = 1) : d298645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31343, d298645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31343, d298645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31344 q = 1) (hb : d261985 q = 1) : d298646 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31344, d298646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31344, d298646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31345 q = 1) (hb : d261985 q = 1) : d298647 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31345, d298647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31345, d298647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31346 q = 1) (hb : d261985 q = 1) : d298648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31346, d298648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31346, d298648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31347 q = 1) (hb : d261985 q = 1) : d298649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31347, d298649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31347, d298649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76935 (p : Pattern) (ha : d31417 p = 1) (hb : d261985 p = 1) : d298655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31414 q = 1) (hb : d261985 q = 1) : d298652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31414, d298652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31414, d298652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31415 q = 1) (hb : d261985 q = 1) : d298653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31415, d298653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31415, d298653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31416 q = 1) (hb : d261985 q = 1) : d298654 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31416, d298654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31416, d298654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31417 q = 1) (hb : d261985 q = 1) : d298655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31417, d298655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31417, d298655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76936 (p : Pattern) (ha : d245471 p = 1) (hb : d261985 p = 1) : d298661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31289 q = 1) (hb : d261985 q = 1) : d298594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31289, d298594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76922 q ha hb
    | true =>
      simp only [d31289, d298594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76923 q ha hb
  have h2 (q : Pattern) (ha : d31290 q = 1) (hb : d261985 q = 1) : d298595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31290, d298595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31290, d298595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31291 q = 1) (hb : d261985 q = 1) : d298596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31291, d298596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31291, d298596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31292 q = 1) (hb : d261985 q = 1) : d298597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31292, d298597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31292, d298597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31299 q = 1) (hb : d261985 q = 1) : d298604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31299, d298604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76924 q ha hb
    | true =>
      simp only [d31299, d298604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76925 q ha hb
  have h6 (q : Pattern) (ha : d31300 q = 1) (hb : d261985 q = 1) : d298605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31300, d298605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31300, d298605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31301 q = 1) (hb : d261985 q = 1) : d298606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31301, d298606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31301, d298606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31348 q = 1) (hb : d261985 q = 1) : d298650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31348, d298650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76934 q ha hb
    | true =>
      simp only [d31348, d298650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76908 q ha hb
  have h9 (q : Pattern) (ha : d245467 q = 1) (hb : d261985 q = 1) : d298651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d298651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245467, d298651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31418 q = 1) (hb : d261985 q = 1) : d298656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31418, d298656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76935 q ha hb
    | true =>
      simp only [d31418, d298656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31419 q = 1) (hb : d261985 q = 1) : d298657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31419, d298657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31419, d298657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245468 q = 1) (hb : d261985 q = 1) : d298658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d298658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245468, d298658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245469 q = 1) (hb : d261985 q = 1) : d298659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d298659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245469, d298659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245470 q = 1) (hb : d261985 q = 1) : d298660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d298660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245470, d298660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245471 q = 1) (hb : d261985 q = 1) : d298661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245471, d298661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245471, d298661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76937 (p : Pattern) (ha : d31424 p = 1) (hb : d261985 p = 1) : d298662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d261985 q = 1) : d298564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d298564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31285 q = 1) (hb : d261985 q = 1) : d298590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31285, d298590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31285, d298590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31424 q = 1) (hb : d261985 q = 1) : d298662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31424, d298662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31424, d298662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76938 (p : Pattern) (ha : d31425 p = 1) (hb : d261985 p = 1) : d298663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d261985 q = 1) : d298568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d298568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31287 q = 1) (hb : d261985 q = 1) : d298592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31287, d298592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31287, d298592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31425 q = 1) (hb : d261985 q = 1) : d298663 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31425, d298663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31425, d298663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76939 (p : Pattern) (ha : d31430 p = 1) (hb : d261985 p = 1) : d298668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d261985 q = 1) : d298563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d298563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31293 q = 1) (hb : d261985 q = 1) : d298598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31293, d298598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31293, d298598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31294 q = 1) (hb : d261985 q = 1) : d298599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31294, d298599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31294, d298599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31430 q = 1) (hb : d261985 q = 1) : d298668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31430, d298668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31430, d298668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76940 (p : Pattern) (ha : d31431 p = 1) (hb : d261985 p = 1) : d298669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d261985 q = 1) : d298561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76907 q ha hb
    | true =>
      simp only [d31256, d298561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d261985 q = 1) : d298562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d298562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d261985 q = 1) : d298567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d298567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31296 q = 1) (hb : d261985 q = 1) : d298601 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31296, d298601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31296, d298601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31297 q = 1) (hb : d261985 q = 1) : d298602 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31297, d298602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31297, d298602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31431 q = 1) (hb : d261985 q = 1) : d298669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31431, d298669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31431, d298669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76941 (p : Pattern) (ha : d31435 p = 1) (hb : d261985 p = 1) : d298673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31342 q = 1) (hb : d261985 q = 1) : d298644 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31342, d298644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76933 q ha hb
    | true =>
      simp only [d31342, d298644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31343 q = 1) (hb : d261985 q = 1) : d298645 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31343, d298645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31343, d298645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31344 q = 1) (hb : d261985 q = 1) : d298646 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31344, d298646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31344, d298646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31345 q = 1) (hb : d261985 q = 1) : d298647 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31345, d298647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31345, d298647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31346 q = 1) (hb : d261985 q = 1) : d298648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31346, d298648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31346, d298648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31435 q = 1) (hb : d261985 q = 1) : d298673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31435, d298673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31435, d298673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76942 (p : Pattern) (ha : d31441 p = 1) (hb : d261985 p = 1) : d298676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d261985 q = 1) : d298557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76906 q ha hb
    | true =>
      simp only [d31252, d298557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d261985 q = 1) : d298558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d298558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31414 q = 1) (hb : d261985 q = 1) : d298652 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31414, d298652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31414, d298652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31415 q = 1) (hb : d261985 q = 1) : d298653 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31415, d298653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31415, d298653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31416 q = 1) (hb : d261985 q = 1) : d298654 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31416, d298654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31416, d298654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31441 q = 1) (hb : d261985 q = 1) : d298676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31441, d298676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31441, d298676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76943 (p : Pattern) (ha : d245476 p = 1) (hb : d261985 p = 1) : d298682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31289 q = 1) (hb : d261985 q = 1) : d298594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31289, d298594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76922 q ha hb
    | true =>
      simp only [d31289, d298594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76923 q ha hb
  have h2 (q : Pattern) (ha : d31290 q = 1) (hb : d261985 q = 1) : d298595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31290, d298595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31290, d298595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31291 q = 1) (hb : d261985 q = 1) : d298596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31291, d298596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31291, d298596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31292 q = 1) (hb : d261985 q = 1) : d298597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31292, d298597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31292, d298597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31299 q = 1) (hb : d261985 q = 1) : d298604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31299, d298604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76924 q ha hb
    | true =>
      simp only [d31299, d298604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76925 q ha hb
  have h6 (q : Pattern) (ha : d31300 q = 1) (hb : d261985 q = 1) : d298605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31300, d298605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31300, d298605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31301 q = 1) (hb : d261985 q = 1) : d298606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31301, d298606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31301, d298606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31348 q = 1) (hb : d261985 q = 1) : d298650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31348, d298650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76934 q ha hb
    | true =>
      simp only [d31348, d298650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76908 q ha hb
  have h9 (q : Pattern) (ha : d245467 q = 1) (hb : d261985 q = 1) : d298651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d298651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245467, d298651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31418 q = 1) (hb : d261985 q = 1) : d298656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31418, d298656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76935 q ha hb
    | true =>
      simp only [d31418, d298656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31419 q = 1) (hb : d261985 q = 1) : d298657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31419, d298657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31419, d298657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245468 q = 1) (hb : d261985 q = 1) : d298658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d298658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245468, d298658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245469 q = 1) (hb : d261985 q = 1) : d298659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d298659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245469, d298659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245470 q = 1) (hb : d261985 q = 1) : d298660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d298660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245470, d298660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31426 q = 1) (hb : d261985 q = 1) : d298664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31426, d298664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76937 q ha hb
    | true =>
      simp only [d31426, d298664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76938 q ha hb
  have h16 (q : Pattern) (ha : d31427 q = 1) (hb : d261985 q = 1) : d298665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31427, d298665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31427, d298665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31428 q = 1) (hb : d261985 q = 1) : d298666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31428, d298666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31428, d298666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31429 q = 1) (hb : d261985 q = 1) : d298667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31429, d298667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31429, d298667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31432 q = 1) (hb : d261985 q = 1) : d298670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31432, d298670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76939 q ha hb
    | true =>
      simp only [d31432, d298670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76940 q ha hb
  have h20 (q : Pattern) (ha : d31433 q = 1) (hb : d261985 q = 1) : d298671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31433, d298671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31433, d298671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31434 q = 1) (hb : d261985 q = 1) : d298672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31434, d298672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31434, d298672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31436 q = 1) (hb : d261985 q = 1) : d298674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31436, d298674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76941 q ha hb
    | true =>
      simp only [d31436, d298674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76911 q ha hb
  have h23 (q : Pattern) (ha : d245472 q = 1) (hb : d261985 q = 1) : d298675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d298675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245472, d298675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31442 q = 1) (hb : d261985 q = 1) : d298677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31442, d298677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76942 q ha hb
    | true =>
      simp only [d31442, d298677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31443 q = 1) (hb : d261985 q = 1) : d298678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31443, d298678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31443, d298678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245473 q = 1) (hb : d261985 q = 1) : d298679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d298679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245473, d298679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245474 q = 1) (hb : d261985 q = 1) : d298680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245474, d298680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245474, d298680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245475 q = 1) (hb : d261985 q = 1) : d298681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245475, d298681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245475, d298681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245476 q = 1) (hb : d261985 q = 1) : d298682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245476, d298682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245476, d298682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro76944 (p : Pattern) (ha : d245483 p = 1) (hb : d261985 p = 1) : d298702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31436 q = 1) (hb : d261985 q = 1) : d298674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31436, d298674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76941 q ha hb
    | true =>
      simp only [d31436, d298674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76911 q ha hb
  have h2 (q : Pattern) (ha : d245472 q = 1) (hb : d261985 q = 1) : d298675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d298675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245472, d298675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31442 q = 1) (hb : d261985 q = 1) : d298677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31442, d298677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76942 q ha hb
    | true =>
      simp only [d31442, d298677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31443 q = 1) (hb : d261985 q = 1) : d298678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31443, d298678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31443, d298678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245473 q = 1) (hb : d261985 q = 1) : d298679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d298679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245473, d298679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245481 q = 1) (hb : d261985 q = 1) : d298700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245481, d298700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245481, d298700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245482 q = 1) (hb : d261985 q = 1) : d298701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245482, d298701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245482, d298701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245483 q = 1) (hb : d261985 q = 1) : d298702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d298702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245483, d298702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76945 (p : Pattern) (ha : d31489 p = 1) (hb : d261985 p = 1) : d298724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31475 q = 1) (hb : d261985 q = 1) : d298710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31475, d298710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31475, d298710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76928 q ha hb
  have h2 (q : Pattern) (ha : d31313 q = 1) (hb : d261985 q = 1) : d298615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31313, d298615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76928 q ha hb
    | true =>
      simp only [d31313, d298615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31476 q = 1) (hb : d261985 q = 1) : d298711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31476, d298711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31476, d298711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31314 q = 1) (hb : d261985 q = 1) : d298616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31314, d298616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31314, d298616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31477 q = 1) (hb : d261985 q = 1) : d298712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31477, d298712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31477, d298712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31478 q = 1) (hb : d261985 q = 1) : d298713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31478, d298713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31478, d298713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31479 q = 1) (hb : d261985 q = 1) : d298714 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31479, d298714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31479, d298714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76929 q ha hb
  have h8 (q : Pattern) (ha : d31318 q = 1) (hb : d261985 q = 1) : d298620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31318, d298620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76929 q ha hb
    | true =>
      simp only [d31318, d298620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31480 q = 1) (hb : d261985 q = 1) : d298715 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31480, d298715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31480, d298715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31319 q = 1) (hb : d261985 q = 1) : d298621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31319, d298621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31319, d298621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31481 q = 1) (hb : d261985 q = 1) : d298716 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31481, d298716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31481, d298716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31482 q = 1) (hb : d261985 q = 1) : d298717 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31482, d298717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31482, d298717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31483 q = 1) (hb : d261985 q = 1) : d298718 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31483, d298718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31483, d298718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31484 q = 1) (hb : d261985 q = 1) : d298719 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31484, d298719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31484, d298719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76930 q ha hb
  have h15 (q : Pattern) (ha : d31326 q = 1) (hb : d261985 q = 1) : d298628 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31326, d298628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76930 q ha hb
    | true =>
      simp only [d31326, d298628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31485 q = 1) (hb : d261985 q = 1) : d298720 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31485, d298720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31485, d298720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31327 q = 1) (hb : d261985 q = 1) : d298629 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31327, d298629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31327, d298629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31486 q = 1) (hb : d261985 q = 1) : d298721 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31486, d298721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31486, d298721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31487 q = 1) (hb : d261985 q = 1) : d298722 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31487, d298722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31487, d298722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31127 q = 1) (hb : d261985 q = 1) : d298465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
  have h21 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31128 q = 1) (hb : d261985 q = 1) : d298466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31129 q = 1) (hb : d261985 q = 1) : d298467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d31130 q = 1) (hb : d261985 q = 1) : d298468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31488 q = 1) (hb : d261985 q = 1) : d298723 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31488, d298723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31488, d298723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31489 q = 1) (hb : d261985 q = 1) : d298724 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31489, d298724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31489, d298724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro76946 (p : Pattern) (ha : d31495 p = 1) (hb : d261985 p = 1) : d298730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31118 q = 1) (hb : d261985 q = 1) : d298456 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31118, d298456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31118, d298456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
  have h2 (q : Pattern) (ha : d30977 q = 1) (hb : d261985 q = 1) : d298361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76875 q ha hb
    | true =>
      simp only [d30977, d298361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31119 q = 1) (hb : d261985 q = 1) : d298457 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31119, d298457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31119, d298457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30978 q = 1) (hb : d261985 q = 1) : d298362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30978, d298362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31120 q = 1) (hb : d261985 q = 1) : d298458 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31120, d298458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31120, d298458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31121 q = 1) (hb : d261985 q = 1) : d298459 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31121, d298459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31121, d298459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31122 q = 1) (hb : d261985 q = 1) : d298460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31122, d298460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31122, d298460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
  have h8 (q : Pattern) (ha : d30982 q = 1) (hb : d261985 q = 1) : d298366 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76876 q ha hb
    | true =>
      simp only [d30982, d298366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31123 q = 1) (hb : d261985 q = 1) : d298461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31123, d298461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31123, d298461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30983 q = 1) (hb : d261985 q = 1) : d298367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30983, d298367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31124 q = 1) (hb : d261985 q = 1) : d298462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31124, d298462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31124, d298462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31125 q = 1) (hb : d261985 q = 1) : d298463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31125, d298463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31125, d298463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31126 q = 1) (hb : d261985 q = 1) : d298464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31126, d298464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31126, d298464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31127 q = 1) (hb : d261985 q = 1) : d298465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
  have h15 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31128 q = 1) (hb : d261985 q = 1) : d298466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31129 q = 1) (hb : d261985 q = 1) : d298467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31130 q = 1) (hb : d261985 q = 1) : d298468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31490 q = 1) (hb : d261985 q = 1) : d298725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
  have h21 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31491 q = 1) (hb : d261985 q = 1) : d298726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31492 q = 1) (hb : d261985 q = 1) : d298727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d31493 q = 1) (hb : d261985 q = 1) : d298728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31494 q = 1) (hb : d261985 q = 1) : d298729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31494, d298729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31494, d298729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31495 q = 1) (hb : d261985 q = 1) : d298730 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31495, d298730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31495, d298730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro76947 (p : Pattern) (ha : d31500 p = 1) (hb : d261985 p = 1) : d298735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31127 q = 1) (hb : d261985 q = 1) : d298465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31127, d298465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
  have h2 (q : Pattern) (ha : d30990 q = 1) (hb : d261985 q = 1) : d298374 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76877 q ha hb
    | true =>
      simp only [d30990, d298374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31128 q = 1) (hb : d261985 q = 1) : d298466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31128, d298466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30991 q = 1) (hb : d261985 q = 1) : d298375 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30991, d298375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31129 q = 1) (hb : d261985 q = 1) : d298467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31129, d298467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31130 q = 1) (hb : d261985 q = 1) : d298468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31130, d298468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31490 q = 1) (hb : d261985 q = 1) : d298725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d298725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
  have h8 (q : Pattern) (ha : d31232 q = 1) (hb : d261985 q = 1) : d298537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76902 q ha hb
    | true =>
      simp only [d31232, d298537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31491 q = 1) (hb : d261985 q = 1) : d298726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31491, d298726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31233 q = 1) (hb : d261985 q = 1) : d298538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31233, d298538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31492 q = 1) (hb : d261985 q = 1) : d298727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31492, d298727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31493 q = 1) (hb : d261985 q = 1) : d298728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31493, d298728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31494 q = 1) (hb : d261985 q = 1) : d298729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31494, d298729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31494, d298729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31499 q = 1) (hb : d261985 q = 1) : d298734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31499, d298734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31500 q = 1) (hb : d261985 q = 1) : d298735 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31500, d298735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31500, d298735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76948 (p : Pattern) (ha : d31516 p = 1) (hb : d261985 p = 1) : d298751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31496 q = 1) (hb : d261985 q = 1) : d298731 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31496, d298731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76945 q ha hb
    | true =>
      simp only [d31496, d298731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76946 q ha hb
  have h2 (q : Pattern) (ha : d31497 q = 1) (hb : d261985 q = 1) : d298732 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31497, d298732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31497, d298732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31498 q = 1) (hb : d261985 q = 1) : d298733 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31498, d298733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31498, d298733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31501 q = 1) (hb : d261985 q = 1) : d298736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31501, d298736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76946 q ha hb
    | true =>
      simp only [d31501, d298736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76947 q ha hb
  have h5 (q : Pattern) (ha : d31502 q = 1) (hb : d261985 q = 1) : d298737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31502, d298737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31502, d298737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31503 q = 1) (hb : d261985 q = 1) : d298738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31503, d298738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31503, d298738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31504 q = 1) (hb : d261985 q = 1) : d298739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31504, d298739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31504, d298739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31507 q = 1) (hb : d261985 q = 1) : d298742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31507, d298742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76946 q ha hb
    | true =>
      simp only [d31507, d298742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76917 q ha hb
  have h9 (q : Pattern) (ha : d31508 q = 1) (hb : d261985 q = 1) : d298743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31508, d298743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31508, d298743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31509 q = 1) (hb : d261985 q = 1) : d298744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31509, d298744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31509, d298744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31511 q = 1) (hb : d261985 q = 1) : d298746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76917 q ha hb
    | true =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76918 q ha hb
  have h12 (q : Pattern) (ha : d31512 q = 1) (hb : d261985 q = 1) : d298747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31513 q = 1) (hb : d261985 q = 1) : d298748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31514 q = 1) (hb : d261985 q = 1) : d298749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31514, d298749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31514, d298749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31515 q = 1) (hb : d261985 q = 1) : d298750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31515, d298750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31515, d298750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31516 q = 1) (hb : d261985 q = 1) : d298751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31516, d298751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31516, d298751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro76949 (p : Pattern) (ha : d31521 p = 1) (hb : d261985 p = 1) : d298756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31507 q = 1) (hb : d261985 q = 1) : d298742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31507, d298742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76946 q ha hb
    | true =>
      simp only [d31507, d298742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76917 q ha hb
  have h2 (q : Pattern) (ha : d31508 q = 1) (hb : d261985 q = 1) : d298743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31508, d298743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31508, d298743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31509 q = 1) (hb : d261985 q = 1) : d298744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31509, d298744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31509, d298744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31511 q = 1) (hb : d261985 q = 1) : d298746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76917 q ha hb
    | true =>
      simp only [d31511, d298746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76918 q ha hb
  have h5 (q : Pattern) (ha : d31512 q = 1) (hb : d261985 q = 1) : d298747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d298747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31513 q = 1) (hb : d261985 q = 1) : d298748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d298748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31514 q = 1) (hb : d261985 q = 1) : d298749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31514, d298749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31514, d298749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31519 q = 1) (hb : d261985 q = 1) : d298754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31519, d298754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31519, d298754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31520 q = 1) (hb : d261985 q = 1) : d298755 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31520, d298755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31520, d298755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31521 q = 1) (hb : d261985 q = 1) : d298756 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31521, d298756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31521, d298756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro76950 (p : Pattern) (ha : d31527 p = 1) (hb : d261985 p = 1) : d298762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31517 q = 1) (hb : d261985 q = 1) : d298752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31517, d298752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76948 q ha hb
    | true =>
      simp only [d31517, d298752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31518 q = 1) (hb : d261985 q = 1) : d298753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31518, d298753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31518, d298753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31522 q = 1) (hb : d261985 q = 1) : d298757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76949 q ha hb
    | true =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31523 q = 1) (hb : d261985 q = 1) : d298758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31524 q = 1) (hb : d261985 q = 1) : d298759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31524, d298759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31524, d298759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31525 q = 1) (hb : d261985 q = 1) : d298760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31525, d298760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31525, d298760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31526 q = 1) (hb : d261985 q = 1) : d298761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31526, d298761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31526, d298761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31527 q = 1) (hb : d261985 q = 1) : d298762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31527, d298762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31527, d298762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76951 (p : Pattern) (ha : d31535 p = 1) (hb : d261985 p = 1) : d298770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31522 q = 1) (hb : d261985 q = 1) : d298757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76949 q ha hb
    | true =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31523 q = 1) (hb : d261985 q = 1) : d298758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31530 q = 1) (hb : d261985 q = 1) : d298765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31530, d298765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76919 q ha hb
    | true =>
      simp only [d31530, d298765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31531 q = 1) (hb : d261985 q = 1) : d298766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31531, d298766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31531, d298766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31532 q = 1) (hb : d261985 q = 1) : d298767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31532, d298767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31532, d298767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31533 q = 1) (hb : d261985 q = 1) : d298768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31533, d298768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31533, d298768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31534 q = 1) (hb : d261985 q = 1) : d298769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31534, d298769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31534, d298769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31535 q = 1) (hb : d261985 q = 1) : d298770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31535, d298770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31535, d298770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76952 (p : Pattern) (ha : d31589 p = 1) (hb : d261985 p = 1) : d298776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31522 q = 1) (hb : d261985 q = 1) : d298757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76949 q ha hb
    | true =>
      simp only [d31522, d298757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31523 q = 1) (hb : d261985 q = 1) : d298758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d298758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31586 q = 1) (hb : d261985 q = 1) : d298773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31586, d298773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31586, d298773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31587 q = 1) (hb : d261985 q = 1) : d298774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31587, d298774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31587, d298774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31588 q = 1) (hb : d261985 q = 1) : d298775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31588, d298775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31588, d298775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31589 q = 1) (hb : d261985 q = 1) : d298776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31589, d298776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31589, d298776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76953 (p : Pattern) (ha : d245493 p = 1) (hb : d261985 p = 1) : d298782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31536 q = 1) (hb : d261985 q = 1) : d298771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31536, d298771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76950 q ha hb
    | true =>
      simp only [d31536, d298771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76951 q ha hb
  have h2 (q : Pattern) (ha : d245489 q = 1) (hb : d261985 q = 1) : d298772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d298772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245489, d298772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31590 q = 1) (hb : d261985 q = 1) : d298777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31590, d298777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76952 q ha hb
    | true =>
      simp only [d31590, d298777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31591 q = 1) (hb : d261985 q = 1) : d298778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31591, d298778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31591, d298778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245490 q = 1) (hb : d261985 q = 1) : d298779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d298779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245490, d298779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245491 q = 1) (hb : d261985 q = 1) : d298780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d298780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245491, d298780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245492 q = 1) (hb : d261985 q = 1) : d298781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d298781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245492, d298781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245493 q = 1) (hb : d261985 q = 1) : d298782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d298782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245493, d298782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76954 (p : Pattern) (ha : d245499 p = 1) (hb : d261985 p = 1) : d298799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31272 q = 1) (hb : d261985 q = 1) : d298577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31272, d298577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31272, d298577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76910 q ha hb
  have h2 (q : Pattern) (ha : d31273 q = 1) (hb : d261985 q = 1) : d298578 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31273, d298578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31273, d298578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31282 q = 1) (hb : d261985 q = 1) : d298587 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76910 q ha hb
    | true =>
      simp only [d31282, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76913 q ha hb
  have h4 (q : Pattern) (ha : d31283 q = 1) (hb : d261985 q = 1) : d298588 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31283, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31284 q = 1) (hb : d261985 q = 1) : d298589 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d31284, d298589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31284, d298589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245477 q = 1) (hb : d261985 q = 1) : d298683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245477, d298683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76936 q ha hb
    | true =>
      simp only [d245477, d298683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76943 q ha hb
  have h7 (q : Pattern) (ha : d31461 q = 1) (hb : d261985 q = 1) : d298696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31461, d298696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76914 q ha hb
    | true =>
      simp only [d31461, d298696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76915 q ha hb
  have h8 (q : Pattern) (ha : d245478 q = 1) (hb : d261985 q = 1) : d298697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245478, d298697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245478, d298697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245479 q = 1) (hb : d261985 q = 1) : d298698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d298698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245479, d298698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245480 q = 1) (hb : d261985 q = 1) : d298699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d298699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245480, d298699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245484 q = 1) (hb : d261985 q = 1) : d298703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d298703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245484, d298703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76944 q ha hb
  have h12 (q : Pattern) (ha : d31470 q = 1) (hb : d261985 q = 1) : d298705 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31470, d298705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31470, d298705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76916 q ha hb
  have h13 (q : Pattern) (ha : d245485 q = 1) (hb : d261985 q = 1) : d298706 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d298706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245485, d298706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245486 q = 1) (hb : d261985 q = 1) : d298707 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d298707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245486, d298707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245487 q = 1) (hb : d261985 q = 1) : d298708 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d298708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245487, d298708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245488 q = 1) (hb : d261985 q = 1) : d298709 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d298709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245488, d298709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245494 q = 1) (hb : d261985 q = 1) : d298783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d298783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245494, d298783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76953 q ha hb
  have h18 (q : Pattern) (ha : d31607 q = 1) (hb : d261985 q = 1) : d298794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31607, d298794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31607, d298794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76921 q ha hb
  have h19 (q : Pattern) (ha : d245495 q = 1) (hb : d261985 q = 1) : d298795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d298795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245495, d298795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245496 q = 1) (hb : d261985 q = 1) : d298796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d298796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245496, d298796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245497 q = 1) (hb : d261985 q = 1) : d298797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d298797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245497, d298797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245498 q = 1) (hb : d261985 q = 1) : d298798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d298798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245498, d298798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245499 q = 1) (hb : d261985 q = 1) : d298799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d298799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245499, d298799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro76955 (p : Pattern) (ha : d245505 p = 1) (hb : d261985 p = 1) : d298805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245500 q = 1) (hb : d261985 q = 1) : d298800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d298800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245500, d298800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76954 q ha hb
  have h2 (q : Pattern) (ha : d245501 q = 1) (hb : d261985 q = 1) : d298801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d298801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245501, d298801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245502 q = 1) (hb : d261985 q = 1) : d298802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d298802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245502, d298802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245503 q = 1) (hb : d261985 q = 1) : d298803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d298803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245503, d298803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245504 q = 1) (hb : d261985 q = 1) : d298804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d298804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245504, d298804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245505 q = 1) (hb : d261985 q = 1) : d298805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d298805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245505, d298805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76956 (p : Pattern) (ha : d31626 p = 1) (hb : d261985 p = 1) : d298811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76927 q ha hb
    | true =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31304 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31305 q = 1) (hb : d261985 q = 1) : d298607 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28880 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76926 q ha hb
    | true =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28881 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25765 q = 1) (hb : d261985 q = 1) : d264590 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66078 q ha hb
    | true =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25766 q = 1) (hb : d261985 q = 1) : d264591 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31306 q = 1) (hb : d261985 q = 1) : d298608 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31307 q = 1) (hb : d261985 q = 1) : d298609 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31308 q = 1) (hb : d261985 q = 1) : d298610 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31623 q = 1) (hb : d261985 q = 1) : d298808 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d31309 q = 1) (hb : d261985 q = 1) : d298611 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31309, d298611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31309, d298611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31624 q = 1) (hb : d261985 q = 1) : d298809 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31624, d298809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31624, d298809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31625 q = 1) (hb : d261985 q = 1) : d298810 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31625, d298810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31625, d298810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31626 q = 1) (hb : d261985 q = 1) : d298811 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31626, d298811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31626, d298811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro76957 (p : Pattern) (ha : d31636 p = 1) (hb : d261985 p = 1) : d298821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d261985 q = 1) : d298808 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30971 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76874 q ha hb
    | true =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30972 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30973 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31631 q = 1) (hb : d261985 q = 1) : d298816 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d298816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d298816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31632 q = 1) (hb : d261985 q = 1) : d298817 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d298817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31632, d298817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31633 q = 1) (hb : d261985 q = 1) : d298818 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d31634 q = 1) (hb : d261985 q = 1) : d298819 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31635 q = 1) (hb : d261985 q = 1) : d298820 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d31636 q = 1) (hb : d261985 q = 1) : d298821 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31636, d298821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31636, d298821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro76958 (p : Pattern) (ha : d31642 p = 1) (hb : d261985 p = 1) : d298827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31323 q = 1) (hb : d261985 q = 1) : d298625 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31324 q = 1) (hb : d261985 q = 1) : d298626 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31633 q = 1) (hb : d261985 q = 1) : d298818 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31634 q = 1) (hb : d261985 q = 1) : d298819 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31635 q = 1) (hb : d261985 q = 1) : d298820 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31642 q = 1) (hb : d261985 q = 1) : d298827 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31642, d298827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31642, d298827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro76959 (p : Pattern) (ha : d31649 p = 1) (hb : d261985 p = 1) : d298834 p = 1 := by
  have h0 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d31633 q = 1) (hb : d261985 q = 1) : d298818 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25435 q = 1) (hb : d261985 q = 1) : d264047 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25435, d264047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25435, d264047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d31647 q = 1) (hb : d261985 q = 1) : d298832 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31647, d298832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31647, d298832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31648 q = 1) (hb : d261985 q = 1) : d298833 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31648, d298833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31648, d298833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d1119 q = 1) (hb : d261985 q = 1) : d1119 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31649 q = 1) (hb : d261985 q = 1) : d298834 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31649, d298834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31649, d298834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76960 (p : Pattern) (ha : d31655 p = 1) (hb : d261985 p = 1) : d298840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31627 q = 1) (hb : d261985 q = 1) : d298812 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d298812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76956 q ha hb
    | true =>
      simp only [d31627, d298812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31628 q = 1) (hb : d261985 q = 1) : d298813 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d298813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31628, d298813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31629 q = 1) (hb : d261985 q = 1) : d298814 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31629, d298814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31629, d298814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31630 q = 1) (hb : d261985 q = 1) : d298815 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31630, d298815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31630, d298815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31637 q = 1) (hb : d261985 q = 1) : d298822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d298822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76957 q ha hb
    | true =>
      simp only [d31637, d298822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31638 q = 1) (hb : d261985 q = 1) : d298823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d298823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31638, d298823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31639 q = 1) (hb : d261985 q = 1) : d298824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31639, d298824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31639, d298824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31640 q = 1) (hb : d261985 q = 1) : d298825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31640, d298825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31640, d298825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31641 q = 1) (hb : d261985 q = 1) : d298826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31641, d298826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31641, d298826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31643 q = 1) (hb : d261985 q = 1) : d298828 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d298828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76958 q ha hb
    | true =>
      simp only [d31643, d298828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31644 q = 1) (hb : d261985 q = 1) : d298829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d298829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31644, d298829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31645 q = 1) (hb : d261985 q = 1) : d298830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d298830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31645, d298830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31646 q = 1) (hb : d261985 q = 1) : d298831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d298831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31646, d298831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31650 q = 1) (hb : d261985 q = 1) : d298835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76959 q ha hb
    | true =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31651 q = 1) (hb : d261985 q = 1) : d298836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31652 q = 1) (hb : d261985 q = 1) : d298837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31653 q = 1) (hb : d261985 q = 1) : d298838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31654 q = 1) (hb : d261985 q = 1) : d298839 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31654, d298839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31654, d298839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31655 q = 1) (hb : d261985 q = 1) : d298840 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31655, d298840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31655, d298840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76961 (p : Pattern) (ha : d31661 p = 1) (hb : d261985 p = 1) : d298846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d261985 q = 1) : d298808 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30971 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76874 q ha hb
    | true =>
      simp only [d30971, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30972 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30972, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30973 q = 1) (hb : d261985 q = 1) : d298182 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30973, d298182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31631 q = 1) (hb : d261985 q = 1) : d298816 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d298816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d298816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31632 q = 1) (hb : d261985 q = 1) : d298817 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d298817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31632, d298817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18 q = 1) (hb : d261985 q = 1) : d18 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31656 q = 1) (hb : d261985 q = 1) : d298841 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d298841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d31656, d298841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31657 q = 1) (hb : d261985 q = 1) : d298842 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d298842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31657, d298842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d31658 q = 1) (hb : d261985 q = 1) : d298843 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d298843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31658, d298843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31659 q = 1) (hb : d261985 q = 1) : d298844 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d298844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d31659, d298844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31660 q = 1) (hb : d261985 q = 1) : d298845 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d298845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31660, d298845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31661 q = 1) (hb : d261985 q = 1) : d298846 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31661, d298846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31661, d298846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro76962 (p : Pattern) (ha : d31666 p = 1) (hb : d261985 p = 1) : d298851 p = 1 := by
  have h0 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18 q = 1) (hb : d261985 q = 1) : d18 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31656 q = 1) (hb : d261985 q = 1) : d298841 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d298841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d31656, d298841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31657 q = 1) (hb : d261985 q = 1) : d298842 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d298842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31657, d298842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d31658 q = 1) (hb : d261985 q = 1) : d298843 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d298843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31658, d298843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d261985 q = 1) : d20 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30635 q = 1) (hb : d261985 q = 1) : d298073 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30635, d298073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31659 q = 1) (hb : d261985 q = 1) : d298844 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d298844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31659, d298844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31660 q = 1) (hb : d261985 q = 1) : d298845 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d298845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31660, d298845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1119 q = 1) (hb : d261985 q = 1) : d1119 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31666 q = 1) (hb : d261985 q = 1) : d298851 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31666, d298851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31666, d298851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76963 (p : Pattern) (ha : d31673 p = 1) (hb : d261985 p = 1) : d298858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31662 q = 1) (hb : d261985 q = 1) : d298847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d298847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76961 q ha hb
    | true =>
      simp only [d31662, d298847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31663 q = 1) (hb : d261985 q = 1) : d298848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d298848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31663, d298848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31664 q = 1) (hb : d261985 q = 1) : d298849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31664, d298849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31664, d298849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31665 q = 1) (hb : d261985 q = 1) : d298850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31665, d298850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31665, d298850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31667 q = 1) (hb : d261985 q = 1) : d298852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
    | true =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31668 q = 1) (hb : d261985 q = 1) : d298853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31669 q = 1) (hb : d261985 q = 1) : d298854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31670 q = 1) (hb : d261985 q = 1) : d298855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31671 q = 1) (hb : d261985 q = 1) : d298856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31671, d298856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31671, d298856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31650 q = 1) (hb : d261985 q = 1) : d298835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76959 q ha hb
    | true =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31651 q = 1) (hb : d261985 q = 1) : d298836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31652 q = 1) (hb : d261985 q = 1) : d298837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31653 q = 1) (hb : d261985 q = 1) : d298838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31672 q = 1) (hb : d261985 q = 1) : d298857 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d298857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31672, d298857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31673 q = 1) (hb : d261985 q = 1) : d298858 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31673, d298858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31673, d298858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76964 (p : Pattern) (ha : d31678 p = 1) (hb : d261985 p = 1) : d298863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d261985 q = 1) : d298852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
    | true =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d261985 q = 1) : d298853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d261985 q = 1) : d298854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d261985 q = 1) : d298855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d261985 q = 1) : d298862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d298862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d298862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d261985 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31678 q = 1) (hb : d261985 q = 1) : d298863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31678, d298863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31678, d298863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro76965 (p : Pattern) (ha : d31685 p = 1) (hb : d261985 p = 1) : d298870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d261985 q = 1) : d298859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76960 q ha hb
    | true =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d261985 q = 1) : d298860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d261985 q = 1) : d298861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d261985 q = 1) : d298864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
    | true =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76964 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d261985 q = 1) : d298865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d261985 q = 1) : d298866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d261985 q = 1) : d298867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31683 q = 1) (hb : d261985 q = 1) : d298868 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d298868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31683, d298868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31684 q = 1) (hb : d261985 q = 1) : d298869 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31684, d298869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31684, d298869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31685 q = 1) (hb : d261985 q = 1) : d298870 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31685, d298870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31685, d298870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro76966 (p : Pattern) (ha : d31689 p = 1) (hb : d261985 p = 1) : d298874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31679 q = 1) (hb : d261985 q = 1) : d298864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
    | true =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76964 q ha hb
  have h2 (q : Pattern) (ha : d31680 q = 1) (hb : d261985 q = 1) : d298865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31681 q = 1) (hb : d261985 q = 1) : d298866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31683 q = 1) (hb : d261985 q = 1) : d298868 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d298868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31683, d298868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31688 q = 1) (hb : d261985 q = 1) : d298873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31688, d298873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31688, d298873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31689 q = 1) (hb : d261985 q = 1) : d298874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31689, d298874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31689, d298874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76967 (p : Pattern) (ha : d31695 p = 1) (hb : d261985 p = 1) : d298880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d261985 q = 1) : d298878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d261985 q = 1) : d298879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d298879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d298879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31695 q = 1) (hb : d261985 q = 1) : d298880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31695, d298880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31695, d298880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76968 (p : Pattern) (ha : d31699 p = 1) (hb : d261985 p = 1) : d298884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d261985 q = 1) : d298881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d261985 q = 1) : d298882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d261985 q = 1) : d298883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d298883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d298883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31699 q = 1) (hb : d261985 q = 1) : d298884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31699, d298884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31699, d298884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76969 (p : Pattern) (ha : d31705 p = 1) (hb : d261985 p = 1) : d298890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d261985 q = 1) : d298885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76967 q ha hb
    | true =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76968 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d261985 q = 1) : d298886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d261985 q = 1) : d298887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d261985 q = 1) : d298888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d261985 q = 1) : d298889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31705 q = 1) (hb : d261985 q = 1) : d298890 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31705, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31705, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76970 (p : Pattern) (ha : d31708 p = 1) (hb : d261985 p = 1) : d298893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d261985 q = 1) : d298878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d261985 q = 1) : d298879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d298879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d298879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31708 q = 1) (hb : d261985 q = 1) : d298893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31708, d298893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31708, d298893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76971 (p : Pattern) (ha : d31709 p = 1) (hb : d261985 p = 1) : d298894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d261985 q = 1) : d298881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d261985 q = 1) : d298882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d261985 q = 1) : d298883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d298883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d298883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31709 q = 1) (hb : d261985 q = 1) : d298894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31709, d298894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31709, d298894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76972 (p : Pattern) (ha : d31715 p = 1) (hb : d261985 p = 1) : d298900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d261985 q = 1) : d298885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76967 q ha hb
    | true =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76968 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d261985 q = 1) : d298886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d261985 q = 1) : d298887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d261985 q = 1) : d298888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d261985 q = 1) : d298889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31710 q = 1) (hb : d261985 q = 1) : d298895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76970 q ha hb
    | true =>
      simp only [d31710, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76971 q ha hb
  have h7 (q : Pattern) (ha : d31711 q = 1) (hb : d261985 q = 1) : d298896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31712 q = 1) (hb : d261985 q = 1) : d298897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31712, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31713 q = 1) (hb : d261985 q = 1) : d298898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31714 q = 1) (hb : d261985 q = 1) : d298899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31715 q = 1) (hb : d261985 q = 1) : d298900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31715, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31715, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76973 (p : Pattern) (ha : d31927 p = 1) (hb : d261985 p = 1) : d299016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d261985 q = 1) : d298885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76967 q ha hb
    | true =>
      simp only [d31700, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76968 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d261985 q = 1) : d298886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d261985 q = 1) : d298887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d261985 q = 1) : d298888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d261985 q = 1) : d298889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31922 q = 1) (hb : d261985 q = 1) : d299011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d299011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76968 q ha hb
    | true =>
      simp only [d31922, d299011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31923 q = 1) (hb : d261985 q = 1) : d299012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d299012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d299012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31924 q = 1) (hb : d261985 q = 1) : d299013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d299013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31924, d299013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31925 q = 1) (hb : d261985 q = 1) : d299014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d299014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d299014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31926 q = 1) (hb : d261985 q = 1) : d299015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d299015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d299015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31927 q = 1) (hb : d261985 q = 1) : d299016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31927, d299016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31927, d299016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76974 (p : Pattern) (ha : d31933 p = 1) (hb : d261985 p = 1) : d299022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31922 q = 1) (hb : d261985 q = 1) : d299011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d299011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76968 q ha hb
    | true =>
      simp only [d31922, d299011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31923 q = 1) (hb : d261985 q = 1) : d299012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d299012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d299012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31924 q = 1) (hb : d261985 q = 1) : d299013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d299013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31924, d299013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31925 q = 1) (hb : d261985 q = 1) : d299014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d299014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d299014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31926 q = 1) (hb : d261985 q = 1) : d299015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d299015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d299015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31928 q = 1) (hb : d261985 q = 1) : d299017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d299017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76971 q ha hb
    | true =>
      simp only [d31928, d299017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31929 q = 1) (hb : d261985 q = 1) : d299018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d299018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d299018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31930 q = 1) (hb : d261985 q = 1) : d299019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d299019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31930, d299019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31931 q = 1) (hb : d261985 q = 1) : d299020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d299020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d299020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31932 q = 1) (hb : d261985 q = 1) : d299021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d299021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d299021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31933 q = 1) (hb : d261985 q = 1) : d299022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31933, d299022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31933, d299022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76975 (p : Pattern) (ha : d31942 p = 1) (hb : d261985 p = 1) : d299031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31928 q = 1) (hb : d261985 q = 1) : d299017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d299017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76971 q ha hb
    | true =>
      simp only [d31928, d299017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31929 q = 1) (hb : d261985 q = 1) : d299018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d299018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d299018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31930 q = 1) (hb : d261985 q = 1) : d299019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d299019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31930, d299019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31931 q = 1) (hb : d261985 q = 1) : d299020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d299020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d299020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31932 q = 1) (hb : d261985 q = 1) : d299021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d299021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d299021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31942 q = 1) (hb : d261985 q = 1) : d299031 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31942, d299031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31942, d299031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76976 (p : Pattern) (ha : d32005 p = 1) (hb : d261985 p = 1) : d299094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31996 q = 1) (hb : d261985 q = 1) : d299085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31996, d299085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31996, d299085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76961 q ha hb
  have h2 (q : Pattern) (ha : d31662 q = 1) (hb : d261985 q = 1) : d298847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d298847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76961 q ha hb
    | true =>
      simp only [d31662, d298847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31997 q = 1) (hb : d261985 q = 1) : d299086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31997, d299086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31997, d299086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31663 q = 1) (hb : d261985 q = 1) : d298848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d298848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31663, d298848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31998 q = 1) (hb : d261985 q = 1) : d299087 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31998, d299087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31998, d299087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31999 q = 1) (hb : d261985 q = 1) : d299088 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31999, d299088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31999, d299088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32000 q = 1) (hb : d261985 q = 1) : d299089 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d299089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d299089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
  have h8 (q : Pattern) (ha : d31667 q = 1) (hb : d261985 q = 1) : d298852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
    | true =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32001 q = 1) (hb : d261985 q = 1) : d299090 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d299090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32001, d299090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31668 q = 1) (hb : d261985 q = 1) : d298853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32002 q = 1) (hb : d261985 q = 1) : d299091 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d299091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32002, d299091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32003 q = 1) (hb : d261985 q = 1) : d299092 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d299092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32003, d299092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32004 q = 1) (hb : d261985 q = 1) : d299093 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32004, d299093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32004, d299093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31976 q = 1) (hb : d261985 q = 1) : d299065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d299065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d299065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76959 q ha hb
  have h15 (q : Pattern) (ha : d31650 q = 1) (hb : d261985 q = 1) : d298835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76959 q ha hb
    | true =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31977 q = 1) (hb : d261985 q = 1) : d299066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d299066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31977, d299066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31651 q = 1) (hb : d261985 q = 1) : d298836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31978 q = 1) (hb : d261985 q = 1) : d299067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d299067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31978, d299067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31979 q = 1) (hb : d261985 q = 1) : d299068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d299068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31979, d299068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31990 q = 1) (hb : d261985 q = 1) : d299079 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d299079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31990, d299079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32005 q = 1) (hb : d261985 q = 1) : d299094 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32005, d299094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32005, d299094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro76977 (p : Pattern) (ha : d32010 p = 1) (hb : d261985 p = 1) : d299099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d261985 q = 1) : d299089 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d299089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d299089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d261985 q = 1) : d298852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
    | true =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d261985 q = 1) : d299090 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d299090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d299090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d261985 q = 1) : d298853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d261985 q = 1) : d299091 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d299091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d299091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d261985 q = 1) : d299092 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d299092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d299092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d261985 q = 1) : d299098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d299098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d299098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d261985 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32010 q = 1) (hb : d261985 q = 1) : d299099 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32010, d299099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32010, d299099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro76978 (p : Pattern) (ha : d32029 p = 1) (hb : d261985 p = 1) : d299118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32011 q = 1) (hb : d261985 q = 1) : d299100 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d299100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76976 q ha hb
    | true =>
      simp only [d32011, d299100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76977 q ha hb
  have h2 (q : Pattern) (ha : d32012 q = 1) (hb : d261985 q = 1) : d299101 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d299101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d299101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32013 q = 1) (hb : d261985 q = 1) : d299102 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d299102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d299102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32019 q = 1) (hb : d261985 q = 1) : d299108 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d299108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32019, d299108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32028 q = 1) (hb : d261985 q = 1) : d299117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32028, d299117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32028, d299117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32029 q = 1) (hb : d261985 q = 1) : d299118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32029, d299118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32029, d299118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76979 (p : Pattern) (ha : d32118 p = 1) (hb : d261985 p = 1) : d299150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32030 q = 1) (hb : d261985 q = 1) : d299119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d299119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76978 q ha hb
    | true =>
      simp only [d32030, d299119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32031 q = 1) (hb : d261985 q = 1) : d299120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d299120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d299120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32115 q = 1) (hb : d261985 q = 1) : d299147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32115, d299147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32115, d299147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32116 q = 1) (hb : d261985 q = 1) : d299148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32116, d299148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32116, d299148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32117 q = 1) (hb : d261985 q = 1) : d299149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32117, d299149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32117, d299149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32118 q = 1) (hb : d261985 q = 1) : d299150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32118, d299150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32118, d299150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76980 (p : Pattern) (ha : d32124 p = 1) (hb : d261985 p = 1) : d299156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32119 q = 1) (hb : d261985 q = 1) : d299151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32119, d299151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76979 q ha hb
    | true =>
      simp only [d32119, d299151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32120 q = 1) (hb : d261985 q = 1) : d299152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32120, d299152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32120, d299152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32121 q = 1) (hb : d261985 q = 1) : d299153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32121, d299153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32121, d299153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32122 q = 1) (hb : d261985 q = 1) : d299154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32122, d299154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32122, d299154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32123 q = 1) (hb : d261985 q = 1) : d299155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32123, d299155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32123, d299155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32124 q = 1) (hb : d261985 q = 1) : d299156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32124, d299156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32124, d299156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76981 (p : Pattern) (ha : d31720 p = 1) (hb : d261985 p = 1) : d298905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d261985 q = 1) : d298878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d261985 q = 1) : d298904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d298904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d298904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31720 q = 1) (hb : d261985 q = 1) : d298905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31720, d298905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31720, d298905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76982 (p : Pattern) (ha : d31722 p = 1) (hb : d261985 p = 1) : d298907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d261985 q = 1) : d298881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d261985 q = 1) : d298882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d261985 q = 1) : d298906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d298906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d298906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31722 q = 1) (hb : d261985 q = 1) : d298907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31722, d298907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31722, d298907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76983 (p : Pattern) (ha : d31729 p = 1) (hb : d261985 p = 1) : d298914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d261985 q = 1) : d298912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d298912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d298912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d261985 q = 1) : d298913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d298913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d298913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31729 q = 1) (hb : d261985 q = 1) : d298914 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31729, d298914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31729, d298914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76984 (p : Pattern) (ha : d31732 p = 1) (hb : d261985 p = 1) : d298917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d261985 q = 1) : d298881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d261985 q = 1) : d298915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d298915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d298915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d261985 q = 1) : d298916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d298916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d298916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31732 q = 1) (hb : d261985 q = 1) : d298917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31732, d298917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31732, d298917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76985 (p : Pattern) (ha : d31742 p = 1) (hb : d261985 p = 1) : d298924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76927 q ha hb
    | true =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31304 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31736 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31737 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31738 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31305 q = 1) (hb : d261985 q = 1) : d298607 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25765 q = 1) (hb : d261985 q = 1) : d264590 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66078 q ha hb
    | true =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25766 q = 1) (hb : d261985 q = 1) : d264591 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31739 q = 1) (hb : d261985 q = 1) : d298921 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31739, d298921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31739, d298921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31740 q = 1) (hb : d261985 q = 1) : d298922 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31740, d298922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31740, d298922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31741 q = 1) (hb : d261985 q = 1) : d298923 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31741, d298923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31741, d298923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31742 q = 1) (hb : d261985 q = 1) : d298924 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31742, d298924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31742, d298924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro76986 (p : Pattern) (ha : d31747 p = 1) (hb : d261985 p = 1) : d298929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76927 q ha hb
    | true =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31304 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31305 q = 1) (hb : d261985 q = 1) : d298607 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28880 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76926 q ha hb
    | true =>
      simp only [d28880, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28881 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28881, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25765 q = 1) (hb : d261985 q = 1) : d264590 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66078 q ha hb
    | true =>
      simp only [d25765, d264590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25766 q = 1) (hb : d261985 q = 1) : d264591 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25766, d264591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31306 q = 1) (hb : d261985 q = 1) : d298608 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31306, d298608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31307 q = 1) (hb : d261985 q = 1) : d298609 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31307, d298609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31308 q = 1) (hb : d261985 q = 1) : d298610 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31308, d298610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31323 q = 1) (hb : d261985 q = 1) : d298625 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d31324 q = 1) (hb : d261985 q = 1) : d298626 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31747 q = 1) (hb : d261985 q = 1) : d298929 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31747, d298929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31747, d298929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro76987 (p : Pattern) (ha : d31755 p = 1) (hb : d261985 p = 1) : d298937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31303 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76927 q ha hb
    | true =>
      simp only [d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31304 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31305 q = 1) (hb : d261985 q = 1) : d298607 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31305, d298607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31753 q = 1) (hb : d261985 q = 1) : d298935 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31753, d298935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31753, d298935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31754 q = 1) (hb : d261985 q = 1) : d298936 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31754, d298936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31754, d298936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30745 q = 1) (hb : d261985 q = 1) : d264157 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d30745, d264157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30746 q = 1) (hb : d261985 q = 1) : d264158 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30746, d264158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30969 q = 1) (hb : d261985 q = 1) : d298357 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30969, d298357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31323 q = 1) (hb : d261985 q = 1) : d298625 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31323, d298625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31324 q = 1) (hb : d261985 q = 1) : d298626 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31324, d298626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31755 q = 1) (hb : d261985 q = 1) : d298937 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31755, d298937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31755, d298937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro76988 (p : Pattern) (ha : d31761 p = 1) (hb : d261985 p = 1) : d298943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31743 q = 1) (hb : d261985 q = 1) : d298925 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31743, d298925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76985 q ha hb
    | true =>
      simp only [d31743, d298925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31744 q = 1) (hb : d261985 q = 1) : d298926 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31744, d298926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31744, d298926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31745 q = 1) (hb : d261985 q = 1) : d298927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31745, d298927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31745, d298927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31746 q = 1) (hb : d261985 q = 1) : d298928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31746, d298928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31746, d298928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31748 q = 1) (hb : d261985 q = 1) : d298930 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31748, d298930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76986 q ha hb
    | true =>
      simp only [d31748, d298930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31749 q = 1) (hb : d261985 q = 1) : d298931 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31749, d298931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31749, d298931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31750 q = 1) (hb : d261985 q = 1) : d298932 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31750, d298932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31750, d298932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31751 q = 1) (hb : d261985 q = 1) : d298933 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31751, d298933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31751, d298933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31752 q = 1) (hb : d261985 q = 1) : d298934 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31752, d298934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31752, d298934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31756 q = 1) (hb : d261985 q = 1) : d298938 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31756, d298938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76987 q ha hb
    | true =>
      simp only [d31756, d298938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31757 q = 1) (hb : d261985 q = 1) : d298939 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31757, d298939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31757, d298939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31758 q = 1) (hb : d261985 q = 1) : d298940 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31758, d298940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31758, d298940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31759 q = 1) (hb : d261985 q = 1) : d298941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31759, d298941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31759, d298941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31643 q = 1) (hb : d261985 q = 1) : d298828 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d298828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76958 q ha hb
    | true =>
      simp only [d31643, d298828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31644 q = 1) (hb : d261985 q = 1) : d298829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d298829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31644, d298829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31645 q = 1) (hb : d261985 q = 1) : d298830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d298830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31645, d298830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31646 q = 1) (hb : d261985 q = 1) : d298831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d298831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31646, d298831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31760 q = 1) (hb : d261985 q = 1) : d298942 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31760, d298942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31760, d298942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31761 q = 1) (hb : d261985 q = 1) : d298943 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31761, d298943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31761, d298943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro76989 (p : Pattern) (ha : d31767 p = 1) (hb : d261985 p = 1) : d298949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d261985 q = 1) : d264335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76873 q ha hb
    | true =>
      simp only [d30967, d264335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d261985 q = 1) : d264336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d264336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9771 q = 1) (hb : d261985 q = 1) : d9771 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31621 q = 1) (hb : d261985 q = 1) : d264789 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76834 q ha hb
    | true =>
      simp only [d31621, d264789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d261985 q = 1) : d264790 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31622, d264790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d261985 q = 1) : d298808 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31623, d298808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31765 q = 1) (hb : d261985 q = 1) : d298947 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31765, d298947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31765, d298947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31766 q = 1) (hb : d261985 q = 1) : d298948 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31766, d298948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31766, d298948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25433 q = 1) (hb : d261985 q = 1) : d264045 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66024 q ha hb
    | true =>
      simp only [d25433, d264045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25434 q = 1) (hb : d261985 q = 1) : d264046 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25434, d264046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31633 q = 1) (hb : d261985 q = 1) : d298818 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31633, d298818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31634 q = 1) (hb : d261985 q = 1) : d298819 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31634, d298819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31635 q = 1) (hb : d261985 q = 1) : d298820 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31635, d298820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31767 q = 1) (hb : d261985 q = 1) : d298949 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31767, d298949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31767, d298949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro76990 (p : Pattern) (ha : d31773 p = 1) (hb : d261985 p = 1) : d298955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31768 q = 1) (hb : d261985 q = 1) : d298950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d298950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76989 q ha hb
    | true =>
      simp only [d31768, d298950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31769 q = 1) (hb : d261985 q = 1) : d298951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d298951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31769, d298951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31770 q = 1) (hb : d261985 q = 1) : d298952 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31770, d298952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31770, d298952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31771 q = 1) (hb : d261985 q = 1) : d298953 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31771, d298953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31771, d298953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31650 q = 1) (hb : d261985 q = 1) : d298835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76959 q ha hb
    | true =>
      simp only [d31650, d298835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31651 q = 1) (hb : d261985 q = 1) : d298836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31651, d298836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31652 q = 1) (hb : d261985 q = 1) : d298837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d298837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31653 q = 1) (hb : d261985 q = 1) : d298838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31653, d298838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31772 q = 1) (hb : d261985 q = 1) : d298954 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31772, d298954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31772, d298954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31672 q = 1) (hb : d261985 q = 1) : d298857 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d298857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31672, d298857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31773 q = 1) (hb : d261985 q = 1) : d298955 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31773, d298955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31773, d298955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro76991 (p : Pattern) (ha : d31779 p = 1) (hb : d261985 p = 1) : d298961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31762 q = 1) (hb : d261985 q = 1) : d298944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31762, d298944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76988 q ha hb
    | true =>
      simp only [d31762, d298944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76960 q ha hb
  have h2 (q : Pattern) (ha : d31763 q = 1) (hb : d261985 q = 1) : d298945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31763, d298945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31763, d298945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31764 q = 1) (hb : d261985 q = 1) : d298946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31764, d298946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31764, d298946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31774 q = 1) (hb : d261985 q = 1) : d298956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31774, d298956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76960 q ha hb
    | true =>
      simp only [d31774, d298956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76990 q ha hb
  have h5 (q : Pattern) (ha : d31775 q = 1) (hb : d261985 q = 1) : d298957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31775, d298957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31775, d298957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31776 q = 1) (hb : d261985 q = 1) : d298958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31776, d298958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31776, d298958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31777 q = 1) (hb : d261985 q = 1) : d298959 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31777, d298959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31777, d298959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31674 q = 1) (hb : d261985 q = 1) : d298859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76960 q ha hb
    | true =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
  have h9 (q : Pattern) (ha : d31675 q = 1) (hb : d261985 q = 1) : d298860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31676 q = 1) (hb : d261985 q = 1) : d298861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31679 q = 1) (hb : d261985 q = 1) : d298864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
    | true =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76964 q ha hb
  have h12 (q : Pattern) (ha : d31680 q = 1) (hb : d261985 q = 1) : d298865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31681 q = 1) (hb : d261985 q = 1) : d298866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31682 q = 1) (hb : d261985 q = 1) : d298867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31778 q = 1) (hb : d261985 q = 1) : d298960 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31778, d298960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31778, d298960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31779 q = 1) (hb : d261985 q = 1) : d298961 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31779, d298961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31779, d298961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro76992 (p : Pattern) (ha : d31785 p = 1) (hb : d261985 p = 1) : d298967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d261985 q = 1) : d298962 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d298962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76991 q ha hb
    | true =>
      simp only [d31780, d298962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d261985 q = 1) : d298963 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d298963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d298963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d261985 q = 1) : d298964 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d298964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d298964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d261985 q = 1) : d298965 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d298965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d298965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d261985 q = 1) : d298966 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d298966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d298966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31785 q = 1) (hb : d261985 q = 1) : d298967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31785, d298967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31785, d298967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro76993 (p : Pattern) (ha : d31878 p = 1) (hb : d261985 p = 1) : d298970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d261985 q = 1) : d298852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76962 q ha hb
    | true =>
      simp only [d31667, d298852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d261985 q = 1) : d298853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d298853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d261985 q = 1) : d298854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d298854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d261985 q = 1) : d298855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d298855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d261985 q = 1) : d298862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d298862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d298862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31878 q = 1) (hb : d261985 q = 1) : d298970 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31878, d298970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31878, d298970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76994 (p : Pattern) (ha : d31884 p = 1) (hb : d261985 p = 1) : d298976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d261985 q = 1) : d298859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76960 q ha hb
    | true =>
      simp only [d31674, d298859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d261985 q = 1) : d298860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d298860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d261985 q = 1) : d298861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d298861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d261985 q = 1) : d298864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
    | true =>
      simp only [d31679, d298864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76964 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d261985 q = 1) : d298865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d298865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d261985 q = 1) : d298866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d298866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d261985 q = 1) : d298867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d298867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31879 q = 1) (hb : d261985 q = 1) : d298971 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31879, d298971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76963 q ha hb
    | true =>
      simp only [d31879, d298971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76993 q ha hb
  have h9 (q : Pattern) (ha : d31880 q = 1) (hb : d261985 q = 1) : d298972 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31880, d298972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31880, d298972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31881 q = 1) (hb : d261985 q = 1) : d298973 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31881, d298973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31881, d298973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31882 q = 1) (hb : d261985 q = 1) : d298974 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31882, d298974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31882, d298974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31883 q = 1) (hb : d261985 q = 1) : d298975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31883, d298975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31883, d298975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31884 q = 1) (hb : d261985 q = 1) : d298976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31884, d298976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31884, d298976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro76995 (p : Pattern) (ha : d31890 p = 1) (hb : d261985 p = 1) : d298982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d261985 q = 1) : d298977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d298977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76994 q ha hb
    | true =>
      simp only [d31885, d298977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d261985 q = 1) : d298978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d298978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d298978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d261985 q = 1) : d298979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d298979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d298979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d261985 q = 1) : d298980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d298980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d298980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d261985 q = 1) : d298981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d298981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d298981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31890 q = 1) (hb : d261985 q = 1) : d298982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31890, d298982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31890, d298982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro76996 (p : Pattern) (ha : d245512 p = 1) (hb : d261985 p = 1) : d298988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d261985 q = 1) : d298908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d298908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76981 q ha hb
    | true =>
      simp only [d31723, d298908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76982 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d261985 q = 1) : d298909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d298909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d298909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d261985 q = 1) : d298910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d298910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d298910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d261985 q = 1) : d298911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d298911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d298911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d261985 q = 1) : d298918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d298918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76983 q ha hb
    | true =>
      simp only [d31733, d298918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76984 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d261985 q = 1) : d298919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d298919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d298919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d261985 q = 1) : d298920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d298920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d298920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d261985 q = 1) : d298968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d298968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76992 q ha hb
    | true =>
      simp only [d31786, d298968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76967 q ha hb
  have h9 (q : Pattern) (ha : d245508 q = 1) (hb : d261985 q = 1) : d298969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d298969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245508, d298969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d261985 q = 1) : d298983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d298983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76995 q ha hb
    | true =>
      simp only [d31891, d298983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d261985 q = 1) : d298984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d298984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d298984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245509 q = 1) (hb : d261985 q = 1) : d298985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d298985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d298985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245510 q = 1) (hb : d261985 q = 1) : d298986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d298986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245510, d298986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245511 q = 1) (hb : d261985 q = 1) : d298987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d298987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245511, d298987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245512 q = 1) (hb : d261985 q = 1) : d298988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d298988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d298988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro76997 (p : Pattern) (ha : d31897 p = 1) (hb : d261985 p = 1) : d298989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d261985 q = 1) : d298878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d298878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d261985 q = 1) : d298904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d298904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d298904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31897 q = 1) (hb : d261985 q = 1) : d298989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31897, d298989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31897, d298989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro76998 (p : Pattern) (ha : d31898 p = 1) (hb : d261985 p = 1) : d298990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d261985 q = 1) : d298881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d298881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d261985 q = 1) : d298882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d298882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d261985 q = 1) : d298906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d298906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d298906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31898 q = 1) (hb : d261985 q = 1) : d298990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31898, d298990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31898, d298990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro76999 (p : Pattern) (ha : d31903 p = 1) (hb : d261985 p = 1) : d298995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d261985 q = 1) : d298871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76965 q ha hb
    | true =>
      simp only [d31686, d298871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d261985 q = 1) : d298872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d298872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d261985 q = 1) : d298875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76966 q ha hb
    | true =>
      simp only [d31690, d298875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d261985 q = 1) : d298876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d298876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d261985 q = 1) : d298877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d298877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d261985 q = 1) : d298912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d298912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d298912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d261985 q = 1) : d298913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d298913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d298913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31903 q = 1) (hb : d261985 q = 1) : d298995 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31903, d298995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31903, d298995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
