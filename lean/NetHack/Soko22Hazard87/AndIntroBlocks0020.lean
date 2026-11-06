import NetHack.Soko22Hazard87.AndIntroBlocks0019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro5000 (p : Pattern) (ha : d62803 p = 1) (hb : d73170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d73165 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, d73165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4999 q ha hb
    | true =>
      simp only [d62798, d73165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d73166 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, d73166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, d73166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d73167 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, d73167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, d73167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d73168 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, d73168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, d73168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d73169 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, d73169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, d73169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d73170 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, d73170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, d73170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5001 (p : Pattern) (ha : d62809 p = 1) (hb : d73176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d73171 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, d73171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5000 q ha hb
    | true =>
      simp only [d62804, d73171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d73172 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, d73172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, d73172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d73173 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, d73173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, d73173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d73174 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, d73174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, d73174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d73175 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, d73175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, d73175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d73176 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, d73176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, d73176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5002 (p : Pattern) (ha : d62815 p = 1) (hb : d73182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d73177 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, d73177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5001 q ha hb
    | true =>
      simp only [d62810, d73177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d73178 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, d73178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, d73178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d73179 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, d73179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, d73179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d73180 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, d73180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, d73180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d73181 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, d73181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, d73181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d73182 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, d73182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, d73182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5003 (p : Pattern) (ha : d62821 p = 1) (hb : d73188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d73183 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, d73183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5002 q ha hb
    | true =>
      simp only [d62816, d73183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d73184 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, d73184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, d73184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d73185 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, d73185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, d73185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d73186 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, d73186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, d73186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d73187 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, d73187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, d73187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d73188 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, d73188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, d73188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5004 (p : Pattern) (ha : d95 p = 1) (hb : d62825 p = 1) : d2672 p = 1 := by
  have h0 (q : Pattern) (ha : d65 q = 1) (hb : d53867 q = 1) : d65 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d95 q = 1) (hb : d62825 q = 1) : d2672 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, d62825, d2672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d95, d62825, d2672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5005 (p : Pattern) (ha : d58614 p = 1) (hb : d62825 p = 1) : d62828 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58613 q = 1) : d58613 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58614 q = 1) (hb : d62825 q = 1) : d62828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d62825, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58614, d62825, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5006 (p : Pattern) (ha : d58624 p = 1) (hb : d62825 p = 1) : d62834 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58623 q = 1) : d58623 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58624 q = 1) (hb : d62825 q = 1) : d62834 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d62825, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58624, d62825, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5007 (p : Pattern) (ha : d58630 p = 1) (hb : d62825 p = 1) : d62840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d62825 q = 1) : d2673 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d2673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d2673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5004 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d62825 q = 1) : d2674 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d2674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d2674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d62825 q = 1) : d2675 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d2675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d2675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d62825 q = 1) : d2676 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d2676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d2676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58615 q = 1) (hb : d62825 q = 1) : d62829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58615, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5005 q ha hb
  have h6 (q : Pattern) (ha : d58616 q = 1) (hb : d62825 q = 1) : d62830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58616, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58617 q = 1) (hb : d62825 q = 1) : d62831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58617, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d58618 q = 1) (hb : d62825 q = 1) : d62832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58618, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58619 q = 1) (hb : d62825 q = 1) : d62833 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58619, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58625 q = 1) (hb : d62825 q = 1) : d62835 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58625, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5006 q ha hb
  have h11 (q : Pattern) (ha : d58626 q = 1) (hb : d62825 q = 1) : d62836 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58626, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58627 q = 1) (hb : d62825 q = 1) : d62837 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58627, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58628 q = 1) (hb : d62825 q = 1) : d62838 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58628, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58629 q = 1) (hb : d62825 q = 1) : d62839 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58629, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58630 q = 1) (hb : d62825 q = 1) : d62840 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d58630, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5008 (p : Pattern) (ha : d58635 p = 1) (hb : d62825 p = 1) : d62841 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58634 q = 1) : d58634 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58635 q = 1) (hb : d62825 q = 1) : d62841 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d62825, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58635, d62825, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5009 (p : Pattern) (ha : d58641 p = 1) (hb : d62825 p = 1) : d62847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d62825 q = 1) : d62842 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5008 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d62825 q = 1) : d62843 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d62825 q = 1) : d62844 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d62825 q = 1) : d62845 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d62825 q = 1) : d62846 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d62825 q = 1) : d62847 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5010 (p : Pattern) (ha : d58647 p = 1) (hb : d62825 p = 1) : d62849 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58646 q = 1) : d58646 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4475 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58647 q = 1) (hb : d62825 q = 1) : d62849 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d62825, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58647, d62825, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5011 (p : Pattern) (ha : d58653 p = 1) (hb : d62825 p = 1) : d62855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d62825 q = 1) : d62850 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5010 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d62825 q = 1) : d62851 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d62825 q = 1) : d62852 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d62825 q = 1) : d62853 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d62825 q = 1) : d62854 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d62825 q = 1) : d62855 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5012 (p : Pattern) (ha : d58660 p = 1) (hb : d62825 p = 1) : d62858 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58659 q = 1) : d58659 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58660 q = 1) (hb : d62825 q = 1) : d62858 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d62825, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58660, d62825, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5013 (p : Pattern) (ha : d58666 p = 1) (hb : d62825 p = 1) : d62864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d62825 q = 1) : d62859 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5012 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d62825 q = 1) : d62860 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d62825 q = 1) : d62861 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d62825 q = 1) : d62862 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d62825 q = 1) : d62863 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d62825 q = 1) : d62864 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5014 (p : Pattern) (ha : d58674 p = 1) (hb : d62825 p = 1) : d62868 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58673 q = 1) : d58673 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4554 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58674 q = 1) (hb : d62825 q = 1) : d62868 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d62825, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58674, d62825, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5015 (p : Pattern) (ha : d58680 p = 1) (hb : d62825 p = 1) : d62874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d62825 q = 1) : d62869 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5014 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d62825 q = 1) : d62870 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d62825 q = 1) : d62871 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d62825 q = 1) : d62872 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d62825 q = 1) : d62873 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d62825 q = 1) : d62874 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5016 (p : Pattern) (ha : d58689 p = 1) (hb : d62825 p = 1) : d62879 p = 1 := by
  have h0 (q : Pattern) (ha : d53867 q = 1) (hb : d58688 q = 1) : d58688 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4595 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58689 q = 1) (hb : d62825 q = 1) : d62879 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d62825, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d58689, d62825, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5017 (p : Pattern) (ha : d58695 p = 1) (hb : d62825 p = 1) : d62885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d62825 q = 1) : d62880 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5016 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d62825 q = 1) : d62881 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d62825 q = 1) : d62882 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d62825 q = 1) : d62883 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d62825 q = 1) : d62884 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d62825 q = 1) : d62885 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5018 (p : Pattern) (ha : d58701 p = 1) (hb : d62825 p = 1) : d62891 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d62825 q = 1) : d62848 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5007 q ha hb
    | true =>
      simp only [d58642, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5009 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d62825 q = 1) : d62856 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5011 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d62825 q = 1) : d62857 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d62825 q = 1) : d62865 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5013 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d62825 q = 1) : d62866 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d62825 q = 1) : d62867 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d62825 q = 1) : d62875 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5015 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d62825 q = 1) : d62876 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d62825 q = 1) : d62877 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d62825 q = 1) : d62878 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d62825 q = 1) : d62886 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5017 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d62825 q = 1) : d62887 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d62825 q = 1) : d62888 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d62825 q = 1) : d62889 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d62825 q = 1) : d62890 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d62825 q = 1) : d62891 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5019 (p : Pattern) (ha : d58707 p = 1) (hb : d62825 p = 1) : d62897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d62825 q = 1) : d62892 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5018 q ha hb
    | true =>
      simp only [d58702, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d62825 q = 1) : d62893 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d62825 q = 1) : d62894 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d62825 q = 1) : d62895 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d62825 q = 1) : d62896 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d62825 q = 1) : d62897 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5020 (p : Pattern) (ha : d58713 p = 1) (hb : d62825 p = 1) : d62903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d62825 q = 1) : d62898 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5019 q ha hb
    | true =>
      simp only [d58708, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d62825 q = 1) : d62899 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d62825 q = 1) : d62900 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d62825 q = 1) : d62901 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d62825 q = 1) : d62902 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d62825 q = 1) : d62903 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5021 (p : Pattern) (ha : d58719 p = 1) (hb : d62825 p = 1) : d62909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d62825 q = 1) : d62904 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5020 q ha hb
    | true =>
      simp only [d58714, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d62825 q = 1) : d62905 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d62825 q = 1) : d62906 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d62825 q = 1) : d62907 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d62825 q = 1) : d62908 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d62825 q = 1) : d62909 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5022 (p : Pattern) (ha : d58725 p = 1) (hb : d62825 p = 1) : d62915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d62825 q = 1) : d62910 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5021 q ha hb
    | true =>
      simp only [d58720, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d62825 q = 1) : d62911 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d62825 q = 1) : d62912 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d62825 q = 1) : d62913 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d62825 q = 1) : d62914 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d62825 q = 1) : d62915 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5023 (p : Pattern) (ha : d58731 p = 1) (hb : d62825 p = 1) : d62921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d62825 q = 1) : d62916 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5022 q ha hb
    | true =>
      simp only [d58726, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d62825 q = 1) : d62917 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d62825 q = 1) : d62918 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d62825 q = 1) : d62919 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d62825 q = 1) : d62920 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d62825 q = 1) : d62921 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5024 (p : Pattern) (ha : d58737 p = 1) (hb : d62827 p = 1) : d62927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d62825 q = 1) : d62922 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5023 q ha hb
    | true =>
      simp only [d58732, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d62825 q = 1) : d62923 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d62825 q = 1) : d62924 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d62825 q = 1) : d62925 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d62826 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d58736 q = 1) (hb : d62827 q = 1) : d62926 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d62827, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d62827, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d58737 q = 1) (hb : d62827 q = 1) : d62927 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58737, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5025 (p : Pattern) (ha : d58743 p = 1) (hb : d62827 p = 1) : d62933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d62827 q = 1) : d62928 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5024 q ha hb
    | true =>
      simp only [d58738, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d62827 q = 1) : d62929 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d62827 q = 1) : d62930 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d62827 q = 1) : d62931 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d62827 q = 1) : d62932 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d62827 q = 1) : d62933 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5026 (p : Pattern) (ha : d54192 p = 1) (hb : d62828 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d58610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52033, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d58611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d58612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d52039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d52040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d52041 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d58613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d54192 q = 1) (hb : d62828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54192, d62828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro5027 (p : Pattern) (ha : d54198 p = 1) (hb : d62834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52165 q = 1) (hb : d58620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52165, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52166 q = 1) (hb : d58621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52166, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52167 q = 1) (hb : d58622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4386 q = 1) (hb : d52171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4387 q = 1) (hb : d52174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d52174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4387, d52174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4388 q = 1) (hb : d52175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d52175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4388, d52175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4389 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d52176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4389, d52176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52177 q = 1) (hb : d58623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52177, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54198 q = 1) (hb : d62834 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54198, d62834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5028 (p : Pattern) (ha : d54204 p = 1) (hb : d62840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2673 q = 1) (hb : d54188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2673, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro449 q ha hb
  have h2 (q : Pattern) (ha : d2674 q = 1) (hb : d54189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2674, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2675 q = 1) (hb : d54190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2675, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2676 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2676, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54193 q = 1) (hb : d62829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54193, d62829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5026 q ha hb
  have h6 (q : Pattern) (ha : d54194 q = 1) (hb : d62830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54194, d62830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54195 q = 1) (hb : d62831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54195, d62831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54196 q = 1) (hb : d62832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54196, d62832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54197 q = 1) (hb : d62833 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54197, d62833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54199 q = 1) (hb : d62835 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54199, d62835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5027 q ha hb
  have h11 (q : Pattern) (ha : d54200 q = 1) (hb : d62836 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54200, d62836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54201 q = 1) (hb : d62837 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54201, d62837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54202 q = 1) (hb : d62838 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54202, d62838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54203 q = 1) (hb : d62839 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54203, d62839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54204 q = 1) (hb : d62840 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54204, d62840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5029 (p : Pattern) (ha : d54205 p = 1) (hb : d62841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52350 q = 1) (hb : d58631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52350, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52351 q = 1) (hb : d58632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52351, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52352 q = 1) (hb : d58633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4423 q = 1) (hb : d52356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4424 q = 1) (hb : d52359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d52359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4424, d52359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4425 q = 1) (hb : d52360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d52360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4425, d52360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4426 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d52361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4426, d52361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52362 q = 1) (hb : d58634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52362, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54205 q = 1) (hb : d62841 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54205, d62841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5030 (p : Pattern) (ha : d54211 p = 1) (hb : d62847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d62842 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d62842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5029 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d62843 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d62843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d62844 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d62844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d62845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d62845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d62846 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d62846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d62847 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d62847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5031 (p : Pattern) (ha : d54213 p = 1) (hb : d62849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52571 q = 1) (hb : d58643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52571, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52572 q = 1) (hb : d58644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52572, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52573 q = 1) (hb : d58645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4461 q = 1) (hb : d52577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro126 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4462 q = 1) (hb : d52580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d52580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4462, d52580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4463 q = 1) (hb : d52581 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d52581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4463, d52581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4464 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d52582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4464, d52582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52583 q = 1) (hb : d58646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52583, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54213 q = 1) (hb : d62849 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54213, d62849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5032 (p : Pattern) (ha : d54219 p = 1) (hb : d62855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d62850 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d62850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5031 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d62851 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d62851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d62852 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d62852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d62853 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d62853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d62854 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d62854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d62855 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d62855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5033 (p : Pattern) (ha : d54222 p = 1) (hb : d62858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52851 q = 1) (hb : d58656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52851, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52852 q = 1) (hb : d58657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52852, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52853 q = 1) (hb : d58658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4500 q = 1) (hb : d52857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro178 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4501 q = 1) (hb : d52860 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d52860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4501, d52860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4502 q = 1) (hb : d52861 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d52861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4502, d52861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4503 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d52862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4503, d52862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52863 q = 1) (hb : d58659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52863, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54222 q = 1) (hb : d62858 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54222, d62858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5034 (p : Pattern) (ha : d54228 p = 1) (hb : d62864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d62859 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d62859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5033 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d62860 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d62860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d62861 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d62861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d62862 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d62862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d62863 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d62863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d62864 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d62864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5035 (p : Pattern) (ha : d54232 p = 1) (hb : d62868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53166 q = 1) (hb : d58670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53166, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d53167 q = 1) (hb : d58671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53167, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d53168 q = 1) (hb : d58672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4540 q = 1) (hb : d53172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro234 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4541 q = 1) (hb : d53175 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d53175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4541, d53175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4542 q = 1) (hb : d53176 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d53176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4542, d53176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4543 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d53177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4543, d53177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53178 q = 1) (hb : d58673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53178, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54232 q = 1) (hb : d62868 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54232, d62868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5036 (p : Pattern) (ha : d54238 p = 1) (hb : d62874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d62869 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d62869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5035 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d62870 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d62870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d62871 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d62871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d62872 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d62872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d62873 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d62873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d62874 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d62874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5037 (p : Pattern) (ha : d54243 p = 1) (hb : d62879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53483 q = 1) (hb : d58685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53483, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d53484 q = 1) (hb : d58686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53484, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d53485 q = 1) (hb : d58687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4581 q = 1) (hb : d53489 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro293 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4582 q = 1) (hb : d53492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d53492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4582, d53492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4583 q = 1) (hb : d53493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d53493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4583, d53493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4584 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d53494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4584, d53494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53495 q = 1) (hb : d58688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53495, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d54243 q = 1) (hb : d62879 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d54243, d62879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro5038 (p : Pattern) (ha : d54249 p = 1) (hb : d62885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d62880 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d62880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5037 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d62881 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d62881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d62882 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d62882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d62883 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d62883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d62884 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d62884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d62885 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d62885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5039 (p : Pattern) (ha : d54255 p = 1) (hb : d62891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d62848 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5028 q ha hb
    | true =>
      simp only [d54212, d62848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5030 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d62856 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d62856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5032 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d62857 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d62857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d62865 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d62865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5034 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d62866 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d62866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d62867 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d62867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d62875 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d62875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5036 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d62876 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d62876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d62877 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d62877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d62878 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d62878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d62886 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d62886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5038 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d62887 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d62887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d62888 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d62888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d62889 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d62889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d62890 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d62890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d62891 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d62891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5040 (p : Pattern) (ha : d54261 p = 1) (hb : d62897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d62892 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5039 q ha hb
    | true =>
      simp only [d54256, d62892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d62893 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d62893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d62894 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d62894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d62895 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d62895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d62896 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d62896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d62897 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d62897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5041 (p : Pattern) (ha : d54267 p = 1) (hb : d62903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d62898 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5040 q ha hb
    | true =>
      simp only [d54262, d62898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d62899 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d62899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d62900 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d62900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d62901 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d62901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d62902 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d62902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d62903 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d62903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5042 (p : Pattern) (ha : d54273 p = 1) (hb : d62909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d62904 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5041 q ha hb
    | true =>
      simp only [d54268, d62904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d62905 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d62905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d62906 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d62906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d62907 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d62907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d62908 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d62908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d62909 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d62909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5043 (p : Pattern) (ha : d54279 p = 1) (hb : d62915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d62910 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5042 q ha hb
    | true =>
      simp only [d54274, d62910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d62911 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d62911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d62912 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d62912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d62913 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d62913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d62914 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d62914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d62915 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d62915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5044 (p : Pattern) (ha : d54285 p = 1) (hb : d62921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d62916 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5043 q ha hb
    | true =>
      simp only [d54280, d62916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d62917 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d62917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d62918 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d62918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d62919 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d62919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d62920 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d62920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d62921 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d62921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5045 (p : Pattern) (ha : d54291 p = 1) (hb : d62927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d62922 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5044 q ha hb
    | true =>
      simp only [d54286, d62922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d62923 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d62923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d62924 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d62924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d62925 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d62925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d62926 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d62926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d62927 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d62927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5046 (p : Pattern) (ha : d54297 p = 1) (hb : d62933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d62928 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5045 q ha hb
    | true =>
      simp only [d54292, d62928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d62929 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d62929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d62930 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d62930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d62931 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d62931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d62932 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d62932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d62933 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d62933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5047 (p : Pattern) (ha : d53647 p = 1) (hb : d62825 p = 1) : d54404 p = 1 := by
  have h0 (q : Pattern) (ha : d53642 q = 1) (hb : d53867 q = 1) : d53642 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53647 q = 1) (hb : d62825 q = 1) : d54404 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d62825, d54404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53647, d62825, d54404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5048 (p : Pattern) (ha : d53671 p = 1) (hb : d62825 p = 1) : d54410 p = 1 := by
  have h0 (q : Pattern) (ha : d53660 q = 1) (hb : d53867 q = 1) : d53660 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53671 q = 1) (hb : d62825 q = 1) : d54410 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d62825, d54410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53671, d62825, d54410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5049 (p : Pattern) (ha : d53677 p = 1) (hb : d62825 p = 1) : d54416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d62825 q = 1) : d54405 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d54405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d54405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5047 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d62825 q = 1) : d54406 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d54406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d54406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d62825 q = 1) : d54407 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d54407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d54407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d62825 q = 1) : d54408 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d54408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d54408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d62825 q = 1) : d54409 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d54409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d54409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d62825 q = 1) : d54411 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d54411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d54411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5048 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d62825 q = 1) : d54412 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d54412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d54412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d62825 q = 1) : d54413 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d54413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d54413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d62825 q = 1) : d54414 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d54414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d54414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d62825 q = 1) : d54415 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d54415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d54415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d62825 q = 1) : d54416 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d54416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d54416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5050 (p : Pattern) (ha : d53697 p = 1) (hb : d62825 p = 1) : d54417 p = 1 := by
  have h0 (q : Pattern) (ha : d53685 q = 1) (hb : d53867 q = 1) : d53685 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53697 q = 1) (hb : d62825 q = 1) : d54417 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d62825, d54417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53697, d62825, d54417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5051 (p : Pattern) (ha : d53703 p = 1) (hb : d62825 p = 1) : d54423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d62825 q = 1) : d54418 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d54418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d54418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5050 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d62825 q = 1) : d54419 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d54419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d54419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d62825 q = 1) : d54420 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d54420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d54420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d62825 q = 1) : d54421 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d54421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d54421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d62825 q = 1) : d54422 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d54422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d54422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d62825 q = 1) : d54423 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d54423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d54423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5052 (p : Pattern) (ha : d53724 p = 1) (hb : d62825 p = 1) : d54425 p = 1 := by
  have h0 (q : Pattern) (ha : d53712 q = 1) (hb : d53867 q = 1) : d53712 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53724 q = 1) (hb : d62825 q = 1) : d54425 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d62825, d54425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53724, d62825, d54425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5053 (p : Pattern) (ha : d53730 p = 1) (hb : d62825 p = 1) : d54431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d62825 q = 1) : d54426 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d54426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d54426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5052 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d62825 q = 1) : d54427 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d54427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d54427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d62825 q = 1) : d54428 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d54428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d54428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d62825 q = 1) : d54429 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d54429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d54429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d62825 q = 1) : d54430 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d54430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d54430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d62825 q = 1) : d54431 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d54431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d54431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5054 (p : Pattern) (ha : d53752 p = 1) (hb : d62825 p = 1) : d54434 p = 1 := by
  have h0 (q : Pattern) (ha : d53740 q = 1) (hb : d53867 q = 1) : d53740 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53752 q = 1) (hb : d62825 q = 1) : d54434 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d62825, d54434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53752, d62825, d54434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5055 (p : Pattern) (ha : d53758 p = 1) (hb : d62825 p = 1) : d54440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d62825 q = 1) : d54435 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d54435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d54435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5054 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d62825 q = 1) : d54436 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d54436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d54436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d62825 q = 1) : d54437 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d54437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d54437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d62825 q = 1) : d54438 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d54438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d54438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d62825 q = 1) : d54439 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d54439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d54439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d62825 q = 1) : d54440 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d54440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d54440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5056 (p : Pattern) (ha : d53781 p = 1) (hb : d62825 p = 1) : d54444 p = 1 := by
  have h0 (q : Pattern) (ha : d53769 q = 1) (hb : d53867 q = 1) : d53769 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53781 q = 1) (hb : d62825 q = 1) : d54444 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d62825, d54444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53781, d62825, d54444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5057 (p : Pattern) (ha : d53787 p = 1) (hb : d62825 p = 1) : d54450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d62825 q = 1) : d54445 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d54445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d54445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5056 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d62825 q = 1) : d54446 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d54446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d54446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d62825 q = 1) : d54447 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d54447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d54447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d62825 q = 1) : d54448 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d54448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d54448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d62825 q = 1) : d54449 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d54449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d54449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d62825 q = 1) : d54450 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d54450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d54450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5058 (p : Pattern) (ha : d53811 p = 1) (hb : d62825 p = 1) : d54455 p = 1 := by
  have h0 (q : Pattern) (ha : d53799 q = 1) (hb : d53867 q = 1) : d53799 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53811 q = 1) (hb : d62825 q = 1) : d54455 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d62825, d54455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53811, d62825, d54455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro5059 (p : Pattern) (ha : d53817 p = 1) (hb : d62825 p = 1) : d54461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d62825 q = 1) : d54456 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d54456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d54456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5058 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d62825 q = 1) : d54457 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d54457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d54457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d62825 q = 1) : d54458 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d54458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d54458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d62825 q = 1) : d54459 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d54459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d54459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d62825 q = 1) : d54460 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d54460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d54460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d62825 q = 1) : d54461 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d54461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d54461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5060 (p : Pattern) (ha : d53823 p = 1) (hb : d62825 p = 1) : d54467 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d62825 q = 1) : d54424 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d54424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5049 q ha hb
    | true =>
      simp only [d53704, d54424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5051 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d62825 q = 1) : d54432 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d54432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d54432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5053 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d62825 q = 1) : d54433 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d54433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d54433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d62825 q = 1) : d54441 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d54441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d54441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5055 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d62825 q = 1) : d54442 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d54442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d54442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d62825 q = 1) : d54443 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d54443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d54443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d62825 q = 1) : d54451 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d54451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d54451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5057 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d62825 q = 1) : d54452 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d54452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d54452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d62825 q = 1) : d54453 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d54453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d54453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d62825 q = 1) : d54454 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d54454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d54454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d62825 q = 1) : d54462 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d54462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d54462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5059 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d62825 q = 1) : d54463 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d54463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d54463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d62825 q = 1) : d54464 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d54464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d54464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d62825 q = 1) : d54465 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d54465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d54465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d62825 q = 1) : d54466 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d54466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d54466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d62825 q = 1) : d54467 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d54467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d54467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5061 (p : Pattern) (ha : d53829 p = 1) (hb : d62825 p = 1) : d54473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d62825 q = 1) : d54468 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d54468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5060 q ha hb
    | true =>
      simp only [d53824, d54468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d62825 q = 1) : d54469 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d54469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d54469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d62825 q = 1) : d54470 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d54470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d54470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d62825 q = 1) : d54471 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d54471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d54471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d62825 q = 1) : d54472 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d54472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d54472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d62825 q = 1) : d54473 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d54473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d54473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5062 (p : Pattern) (ha : d53835 p = 1) (hb : d62825 p = 1) : d54479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d62825 q = 1) : d54474 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d54474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5061 q ha hb
    | true =>
      simp only [d53830, d54474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d62825 q = 1) : d54475 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d54475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d54475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d62825 q = 1) : d54476 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d54476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d54476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d62825 q = 1) : d54477 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d54477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d54477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d62825 q = 1) : d54478 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d54478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d54478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d62825 q = 1) : d54479 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d54479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d54479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5063 (p : Pattern) (ha : d53841 p = 1) (hb : d62825 p = 1) : d54485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d62825 q = 1) : d54480 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d54480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5062 q ha hb
    | true =>
      simp only [d53836, d54480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d62825 q = 1) : d54481 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d54481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d54481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d62825 q = 1) : d54482 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d54482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d54482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d62825 q = 1) : d54483 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d54483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d54483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d62825 q = 1) : d54484 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d54484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d54484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d62825 q = 1) : d54485 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d54485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d54485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5064 (p : Pattern) (ha : d53847 p = 1) (hb : d62825 p = 1) : d54491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d62825 q = 1) : d54486 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d54486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5063 q ha hb
    | true =>
      simp only [d53842, d54486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d62825 q = 1) : d54487 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d54487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d54487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d62825 q = 1) : d54488 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d54488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d54488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d62825 q = 1) : d54489 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d54489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d54489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d62825 q = 1) : d54490 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d54490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d54490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d62825 q = 1) : d54491 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d54491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d54491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5065 (p : Pattern) (ha : d53853 p = 1) (hb : d62825 p = 1) : d54497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d62825 q = 1) : d54492 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d54492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5064 q ha hb
    | true =>
      simp only [d53848, d54492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d62825 q = 1) : d54493 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d54493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d54493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d62825 q = 1) : d54494 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d54494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d54494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d62825 q = 1) : d54495 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d54495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d54495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d62825 q = 1) : d54496 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d54496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d54496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d62825 q = 1) : d54497 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d54497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d54497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5066 (p : Pattern) (ha : d53859 p = 1) (hb : d62827 p = 1) : d54503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d62825 q = 1) : d54498 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d54498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5065 q ha hb
    | true =>
      simp only [d53854, d54498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d62825 q = 1) : d54499 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d54499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d54499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d62825 q = 1) : d54500 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d54500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d54500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d62825 q = 1) : d54501 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d54501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d54501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d62826 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53858 q = 1) (hb : d62827 q = 1) : d54502 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d62827, d54502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d62827, d54502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d62827 q = 1) : d54503 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d54503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53859, d54503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5067 (p : Pattern) (ha : d53865 p = 1) (hb : d62827 p = 1) : d54509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d62827 q = 1) : d54504 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d54504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5066 q ha hb
    | true =>
      simp only [d53860, d54504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d62827 q = 1) : d54505 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d54505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d54505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d62827 q = 1) : d54506 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d54506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d54506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d62827 q = 1) : d54507 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d54507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d54507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d62827 q = 1) : d54508 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d54508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d54508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d62827 q = 1) : d54509 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d54509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d54509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5068 (p : Pattern) (ha : d58433 p = 1) (hb : d58743 p = 1) : d58743 p = 1 := by
  have h0 (q : Pattern) (ha : d58433 q = 1) (hb : d58743 q = 1) : d58743 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro5069 (p : Pattern) (ha : d104 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5070 (p : Pattern) (ha : d111 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d107 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d108 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d109 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d110 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d111 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5071 (p : Pattern) (ha : d4349 p = 1) (hb : d73190 p = 1) : d69447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4340 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51 q = 1) (hb : d73190 q = 1) : d51 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4341 q = 1) (hb : d73190 q = 1) : d69437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4342 q = 1) (hb : d73190 q = 1) : d69445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4343 q = 1) (hb : d73190 q = 1) : d69446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4349 q = 1) (hb : d73190 q = 1) : d69447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5072 (p : Pattern) (ha : d4359 p = 1) (hb : d73190 p = 1) : d69456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d243 q = 1) : d243 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244 q = 1) (hb : d58747 q = 1) : d451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4355 q = 1) (hb : d73190 q = 1) : d452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d73190, d452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4355, d73190, d452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85 q = 1) (hb : d73190 q = 1) : d85 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4356 q = 1) (hb : d73190 q = 1) : d69453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4356, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4357 q = 1) (hb : d73190 q = 1) : d69454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4358 q = 1) (hb : d73190 q = 1) : d69455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4359 q = 1) (hb : d73190 q = 1) : d69456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5073 (p : Pattern) (ha : d51643 p = 1) (hb : d73190 p = 1) : d73194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4335 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44 q = 1) (hb : d73190 q = 1) : d44 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4336 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51641 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51641, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51642 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51642, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51643 q = 1) (hb : d73190 q = 1) : d73194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5074 (p : Pattern) (ha : d51646 p = 1) (hb : d73190 p = 1) : d73195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4335 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44 q = 1) (hb : d73190 q = 1) : d44 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4336 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51641 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51641, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51642 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51642, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d195 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d196 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d197 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d198 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d200 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d201 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d202 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4340 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d51 q = 1) (hb : d73190 q = 1) : d51 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4341 q = 1) (hb : d73190 q = 1) : d69437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51644 q = 1) (hb : d73190 q = 1) : d69445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51644, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51645 q = 1) (hb : d73190 q = 1) : d69446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51645, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51646 q = 1) (hb : d73190 q = 1) : d73195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51646, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5075 (p : Pattern) (ha : d58614 p = 1) (hb : d73191 p = 1) : d73201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d106 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5070 q ha hb
  have h5 (q : Pattern) (ha : d113 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d114 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51647 q = 1) (hb : d73190 q = 1) : d73196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5073 q ha hb
    | true =>
      simp only [d51647, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5074 q ha hb
  have h8 (q : Pattern) (ha : d58610 q = 1) (hb : d73191 q = 1) : d73197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58610, d73191, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58610, d73191, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58611 q = 1) (hb : d73191 q = 1) : d73198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58611, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58611, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58612 q = 1) (hb : d73191 q = 1) : d73199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58612, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58612, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4350 q = 1) (hb : d73190 q = 1) : d69448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5071 q ha hb
  have h13 (q : Pattern) (ha : d4351 q = 1) (hb : d73191 q = 1) : d69449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d73191, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4351, d73191, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4352 q = 1) (hb : d73191 q = 1) : d69450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4353 q = 1) (hb : d73191 q = 1) : d69451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58613 q = 1) (hb : d73191 q = 1) : d73200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58613, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58613, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4360 q = 1) (hb : d73190 q = 1) : d69457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5072 q ha hb
  have h18 (q : Pattern) (ha : d4361 q = 1) (hb : d73191 q = 1) : d69458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d73191, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4361, d73191, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4362 q = 1) (hb : d73191 q = 1) : d69459 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4363 q = 1) (hb : d73191 q = 1) : d69460 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4364 q = 1) (hb : d73191 q = 1) : d69461 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58614 q = 1) (hb : d73191 q = 1) : d73201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58614, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5076 (p : Pattern) (ha : d284 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5077 (p : Pattern) (ha : d291 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d287 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d288 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d289 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d290 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d291 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5078 (p : Pattern) (ha : d4385 p = 1) (hb : d73190 p = 1) : d69484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d385 q = 1) : d385 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d386 q = 1) (hb : d58747 q = 1) : d4725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4376 q = 1) (hb : d73190 q = 1) : d69473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d391 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4377 q = 1) (hb : d73190 q = 1) : d69474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4378 q = 1) (hb : d73190 q = 1) : d69482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4379 q = 1) (hb : d73190 q = 1) : d69483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4385 q = 1) (hb : d73190 q = 1) : d69484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5079 (p : Pattern) (ha : d4395 p = 1) (hb : d73190 p = 1) : d69494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d429 q = 1) : d429 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d430 q = 1) (hb : d58747 q = 1) : d4755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d58747, d4755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d430, d58747, d4755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4391 q = 1) (hb : d73190 q = 1) : d69490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d73190, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4391, d73190, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d452 q = 1) (hb : d73190 q = 1) : d452 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4392 q = 1) (hb : d73190 q = 1) : d69491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4392, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4393 q = 1) (hb : d73190 q = 1) : d69492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4394 q = 1) (hb : d73190 q = 1) : d69493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4395 q = 1) (hb : d73190 q = 1) : d69494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5080 (p : Pattern) (ha : d51660 p = 1) (hb : d73190 p = 1) : d73209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d304 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d305 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4371 q = 1) (hb : d73190 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d371 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4372 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51658 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51658, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51659 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51659, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51660 q = 1) (hb : d73190 q = 1) : d73209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5081 (p : Pattern) (ha : d51663 p = 1) (hb : d73190 p = 1) : d73210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d304 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d305 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4371 q = 1) (hb : d73190 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d371 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4372 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51658 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51658, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51659 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51659, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d377 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d382 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d383 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d384 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d385 q = 1) : d385 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d386 q = 1) (hb : d58747 q = 1) : d4725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4376 q = 1) (hb : d73190 q = 1) : d69473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d391 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4377 q = 1) (hb : d73190 q = 1) : d69474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51661 q = 1) (hb : d73190 q = 1) : d69482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51661, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51662 q = 1) (hb : d73190 q = 1) : d69483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51662, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51663 q = 1) (hb : d73190 q = 1) : d73210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51663, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5082 (p : Pattern) (ha : d58624 p = 1) (hb : d73191 p = 1) : d73216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5076 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5076 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5077 q ha hb
  have h5 (q : Pattern) (ha : d293 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d294 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51664 q = 1) (hb : d73190 q = 1) : d73211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5080 q ha hb
    | true =>
      simp only [d51664, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5081 q ha hb
  have h8 (q : Pattern) (ha : d58620 q = 1) (hb : d73191 q = 1) : d73212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58620, d73191, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58620, d73191, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58621 q = 1) (hb : d73191 q = 1) : d73213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58621, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58621, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58622 q = 1) (hb : d73191 q = 1) : d73214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58622, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58622, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4386 q = 1) (hb : d73190 q = 1) : d69485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5078 q ha hb
  have h13 (q : Pattern) (ha : d4387 q = 1) (hb : d73191 q = 1) : d69486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d73191, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4387, d73191, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4388 q = 1) (hb : d73191 q = 1) : d69487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4389 q = 1) (hb : d73191 q = 1) : d69488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58623 q = 1) (hb : d73191 q = 1) : d73215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58623, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58623, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4396 q = 1) (hb : d73190 q = 1) : d69495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5079 q ha hb
  have h18 (q : Pattern) (ha : d4397 q = 1) (hb : d73191 q = 1) : d69496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d73191, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4397, d73191, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4398 q = 1) (hb : d73191 q = 1) : d69497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4399 q = 1) (hb : d73191 q = 1) : d69498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4400 q = 1) (hb : d73191 q = 1) : d69499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58624 q = 1) (hb : d73191 q = 1) : d73216 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58624, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5083 (p : Pattern) (ha : d58630 p = 1) (hb : d73191 p = 1) : d73222 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d73191 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58615 q = 1) (hb : d73191 q = 1) : d73202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58615, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5075 q ha hb
  have h3 (q : Pattern) (ha : d58616 q = 1) (hb : d73191 q = 1) : d73203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58616, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58617 q = 1) (hb : d73191 q = 1) : d73204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58617, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58618 q = 1) (hb : d73191 q = 1) : d73205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58618, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58619 q = 1) (hb : d73191 q = 1) : d73206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58619, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58625 q = 1) (hb : d73191 q = 1) : d73217 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58625, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5082 q ha hb
  have h8 (q : Pattern) (ha : d58626 q = 1) (hb : d73191 q = 1) : d73218 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58626, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58627 q = 1) (hb : d73191 q = 1) : d73219 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58627, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58628 q = 1) (hb : d73191 q = 1) : d73220 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58628, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58629 q = 1) (hb : d73191 q = 1) : d73221 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58629, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58630 q = 1) (hb : d73191 q = 1) : d73222 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58630, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5084 (p : Pattern) (ha : d497 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d497 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5085 (p : Pattern) (ha : d507 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d494 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d495 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d496 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d503 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d504 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d505 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d506 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d507 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5086 (p : Pattern) (ha : d4422 p = 1) (hb : d73190 p = 1) : d69523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d620 q = 1) : d620 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d621 q = 1) (hb : d58747 q = 1) : d4810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4413 q = 1) (hb : d73190 q = 1) : d69512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d627 q = 1) (hb : d73190 q = 1) : d627 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4414 q = 1) (hb : d73190 q = 1) : d69513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4415 q = 1) (hb : d73190 q = 1) : d69521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4416 q = 1) (hb : d73190 q = 1) : d69522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4422 q = 1) (hb : d73190 q = 1) : d69523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5087 (p : Pattern) (ha : d4432 p = 1) (hb : d73190 p = 1) : d69533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d681 q = 1) : d681 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d690 q = 1) (hb : d58747 q = 1) : d4849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d58747, d4849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d690, d58747, d4849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4428 q = 1) (hb : d73190 q = 1) : d69529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d73190, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4428, d73190, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d721 q = 1) (hb : d73190 q = 1) : d721 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4429 q = 1) (hb : d73190 q = 1) : d69530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4429, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4430 q = 1) (hb : d73190 q = 1) : d69531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4431 q = 1) (hb : d73190 q = 1) : d69532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4432 q = 1) (hb : d73190 q = 1) : d69533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5088 (p : Pattern) (ha : d51685 p = 1) (hb : d73190 p = 1) : d73225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d525 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d526 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d527 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4408 q = 1) (hb : d73190 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d604 q = 1) (hb : d73190 q = 1) : d604 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4409 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51683 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51683, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51684 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51684, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51685 q = 1) (hb : d73190 q = 1) : d73225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5089 (p : Pattern) (ha : d51688 p = 1) (hb : d73190 p = 1) : d73226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d525 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d526 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d527 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4408 q = 1) (hb : d73190 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d604 q = 1) (hb : d73190 q = 1) : d604 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4409 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51683 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51683, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51684 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51684, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d611 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d612 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d612, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d613 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d614 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d617 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d618 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d619 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d620 q = 1) : d620 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d621 q = 1) (hb : d58747 q = 1) : d4810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4413 q = 1) (hb : d73190 q = 1) : d69512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d627 q = 1) (hb : d73190 q = 1) : d627 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4414 q = 1) (hb : d73190 q = 1) : d69513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51686 q = 1) (hb : d73190 q = 1) : d69521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51686, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51687 q = 1) (hb : d73190 q = 1) : d69522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51687, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51688 q = 1) (hb : d73190 q = 1) : d73226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51688, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5090 (p : Pattern) (ha : d58635 p = 1) (hb : d73191 p = 1) : d73232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5084 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d499 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d508 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5084 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5085 q ha hb
  have h5 (q : Pattern) (ha : d509 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d509, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d510 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51689 q = 1) (hb : d73190 q = 1) : d73227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5088 q ha hb
    | true =>
      simp only [d51689, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5089 q ha hb
  have h8 (q : Pattern) (ha : d58631 q = 1) (hb : d73191 q = 1) : d73228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58631, d73191, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58631, d73191, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58632 q = 1) (hb : d73191 q = 1) : d73229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58632, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58632, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58633 q = 1) (hb : d73191 q = 1) : d73230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58633, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58633, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4423 q = 1) (hb : d73190 q = 1) : d69524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5086 q ha hb
  have h13 (q : Pattern) (ha : d4424 q = 1) (hb : d73191 q = 1) : d69525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d73191, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4424, d73191, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4425 q = 1) (hb : d73191 q = 1) : d69526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4426 q = 1) (hb : d73191 q = 1) : d69527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58634 q = 1) (hb : d73191 q = 1) : d73231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58634, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58634, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4433 q = 1) (hb : d73190 q = 1) : d69534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5087 q ha hb
  have h18 (q : Pattern) (ha : d4434 q = 1) (hb : d73191 q = 1) : d69535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d73191, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4434, d73191, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4435 q = 1) (hb : d73191 q = 1) : d69536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4436 q = 1) (hb : d73191 q = 1) : d69537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4437 q = 1) (hb : d73191 q = 1) : d69538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58635 q = 1) (hb : d73191 q = 1) : d73232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58635, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5091 (p : Pattern) (ha : d58641 p = 1) (hb : d73191 p = 1) : d73238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d73191 q = 1) : d73233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5090 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d73191 q = 1) : d73234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d73191 q = 1) : d73235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d73191 q = 1) : d73236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d73191 q = 1) : d73237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d73191 q = 1) : d73238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5092 (p : Pattern) (ha : d789 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d789 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5093 (p : Pattern) (ha : d799 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d796 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d797 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d798 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d799 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5094 (p : Pattern) (ha : d4460 p = 1) (hb : d73190 p = 1) : d69563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d926 q = 1) : d926 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d927 q = 1) (hb : d58747 q = 1) : d4905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4451 q = 1) (hb : d73190 q = 1) : d69552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d933 q = 1) (hb : d73190 q = 1) : d933 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4452 q = 1) (hb : d73190 q = 1) : d69553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4453 q = 1) (hb : d73190 q = 1) : d69561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4454 q = 1) (hb : d73190 q = 1) : d69562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4460 q = 1) (hb : d73190 q = 1) : d69563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5095 (p : Pattern) (ha : d4470 p = 1) (hb : d73190 p = 1) : d69573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1003 q = 1) : d1003 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1011 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1012 q = 1) (hb : d58747 q = 1) : d4944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d58747, d4944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1012, d58747, d4944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4466 q = 1) (hb : d73190 q = 1) : d69569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d73190, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4466, d73190, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1054 q = 1) (hb : d73190 q = 1) : d1054 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4467 q = 1) (hb : d73190 q = 1) : d69570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4467, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4468 q = 1) (hb : d73190 q = 1) : d69571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4469 q = 1) (hb : d73190 q = 1) : d69572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4470 q = 1) (hb : d73190 q = 1) : d69573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5096 (p : Pattern) (ha : d51711 p = 1) (hb : d73190 p = 1) : d73242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d817 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d818 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d819 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4446 q = 1) (hb : d73190 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d910 q = 1) (hb : d73190 q = 1) : d910 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4447 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51709 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51709, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51710 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51710, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51711 q = 1) (hb : d73190 q = 1) : d73242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5097 (p : Pattern) (ha : d51714 p = 1) (hb : d73190 p = 1) : d73243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d817 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d818 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d819 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4446 q = 1) (hb : d73190 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d910 q = 1) (hb : d73190 q = 1) : d910 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4447 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51709 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51709, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51710 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51710, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d917 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d918 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d918, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d919 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d920 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d923 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d924 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d925 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d926 q = 1) : d926 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d927 q = 1) (hb : d58747 q = 1) : d4905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4451 q = 1) (hb : d73190 q = 1) : d69552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d933 q = 1) (hb : d73190 q = 1) : d933 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4452 q = 1) (hb : d73190 q = 1) : d69553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51712 q = 1) (hb : d73190 q = 1) : d69561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51712, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51713 q = 1) (hb : d73190 q = 1) : d69562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51713, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51714 q = 1) (hb : d73190 q = 1) : d73243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51714, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5098 (p : Pattern) (ha : d58647 p = 1) (hb : d73191 p = 1) : d73249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5092 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d791 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d800 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5092 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5093 q ha hb
  have h5 (q : Pattern) (ha : d801 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d801, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d802 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51715 q = 1) (hb : d73190 q = 1) : d73244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5096 q ha hb
    | true =>
      simp only [d51715, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5097 q ha hb
  have h8 (q : Pattern) (ha : d58643 q = 1) (hb : d73191 q = 1) : d73245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58643, d73191, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58643, d73191, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58644 q = 1) (hb : d73191 q = 1) : d73246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58644, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58644, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58645 q = 1) (hb : d73191 q = 1) : d73247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58645, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58645, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4461 q = 1) (hb : d73190 q = 1) : d69564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5094 q ha hb
  have h13 (q : Pattern) (ha : d4462 q = 1) (hb : d73191 q = 1) : d69565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d73191, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4462, d73191, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4463 q = 1) (hb : d73191 q = 1) : d69566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4464 q = 1) (hb : d73191 q = 1) : d69567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58646 q = 1) (hb : d73191 q = 1) : d73248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58646, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58646, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4471 q = 1) (hb : d73190 q = 1) : d69574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5095 q ha hb
  have h18 (q : Pattern) (ha : d4472 q = 1) (hb : d73191 q = 1) : d69575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d73191, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4472, d73191, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4473 q = 1) (hb : d73191 q = 1) : d69576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4474 q = 1) (hb : d73191 q = 1) : d69577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4475 q = 1) (hb : d73191 q = 1) : d69578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58647 q = 1) (hb : d73191 q = 1) : d73249 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58647, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5099 (p : Pattern) (ha : d58653 p = 1) (hb : d73191 p = 1) : d73255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d73191 q = 1) : d73250 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5098 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d73191 q = 1) : d73251 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d73191 q = 1) : d73252 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d73191 q = 1) : d73253 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d73191 q = 1) : d73254 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d73191 q = 1) : d73255 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5100 (p : Pattern) (ha : d1168 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1168 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5101 (p : Pattern) (ha : d1178 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1174 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1175 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1176 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1177 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1178 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5102 (p : Pattern) (ha : d4499 p = 1) (hb : d73190 p = 1) : d69604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1337 q = 1) : d1337 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1338 q = 1) (hb : d58747 q = 1) : d5001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4490 q = 1) (hb : d73190 q = 1) : d69593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1344 q = 1) (hb : d73190 q = 1) : d1344 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4491 q = 1) (hb : d73190 q = 1) : d69594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4492 q = 1) (hb : d73190 q = 1) : d69602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4493 q = 1) (hb : d73190 q = 1) : d69603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4499 q = 1) (hb : d73190 q = 1) : d69604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5103 (p : Pattern) (ha : d4509 p = 1) (hb : d73190 p = 1) : d69614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1428 q = 1) : d1428 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1437 q = 1) (hb : d58747 q = 1) : d5054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d58747, d5054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1437, d58747, d5054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4505 q = 1) (hb : d73190 q = 1) : d69610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d73190, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4505, d73190, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1488 q = 1) (hb : d73190 q = 1) : d1488 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4506 q = 1) (hb : d73190 q = 1) : d69611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4506, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4507 q = 1) (hb : d73190 q = 1) : d69612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4508 q = 1) (hb : d73190 q = 1) : d69613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4509 q = 1) (hb : d73190 q = 1) : d69614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5104 (p : Pattern) (ha : d51738 p = 1) (hb : d73190 p = 1) : d73260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1196 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1197 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1198 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4485 q = 1) (hb : d73190 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1321 q = 1) (hb : d73190 q = 1) : d1321 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4486 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51736 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51736, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51737 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51737, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51738 q = 1) (hb : d73190 q = 1) : d73260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5105 (p : Pattern) (ha : d51741 p = 1) (hb : d73190 p = 1) : d73261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1196 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1197 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1198 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4485 q = 1) (hb : d73190 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1321 q = 1) (hb : d73190 q = 1) : d1321 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4486 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51736 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51736, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51737 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51737, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d1328 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1329 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1329, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d1330 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1331 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d1334 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1335 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d1336 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d1337 q = 1) : d1337 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d1338 q = 1) (hb : d58747 q = 1) : d5001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4490 q = 1) (hb : d73190 q = 1) : d69593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d1344 q = 1) (hb : d73190 q = 1) : d1344 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4491 q = 1) (hb : d73190 q = 1) : d69594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51739 q = 1) (hb : d73190 q = 1) : d69602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51739, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51740 q = 1) (hb : d73190 q = 1) : d69603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51740, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51741 q = 1) (hb : d73190 q = 1) : d73261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51741, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5106 (p : Pattern) (ha : d58660 p = 1) (hb : d73191 p = 1) : d73267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5100 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1170 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1179 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5100 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5101 q ha hb
  have h5 (q : Pattern) (ha : d1180 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1180, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1181 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51742 q = 1) (hb : d73190 q = 1) : d73262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5104 q ha hb
    | true =>
      simp only [d51742, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5105 q ha hb
  have h8 (q : Pattern) (ha : d58656 q = 1) (hb : d73191 q = 1) : d73263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58656, d73191, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58656, d73191, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58657 q = 1) (hb : d73191 q = 1) : d73264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58657, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58658 q = 1) (hb : d73191 q = 1) : d73265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58658, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4500 q = 1) (hb : d73190 q = 1) : d69605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5102 q ha hb
  have h13 (q : Pattern) (ha : d4501 q = 1) (hb : d73191 q = 1) : d69606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d73191, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4501, d73191, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4502 q = 1) (hb : d73191 q = 1) : d69607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4503 q = 1) (hb : d73191 q = 1) : d69608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58659 q = 1) (hb : d73191 q = 1) : d73266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58659, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d73190 q = 1) : d69615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5103 q ha hb
  have h18 (q : Pattern) (ha : d4511 q = 1) (hb : d73191 q = 1) : d69616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d73191, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4511, d73191, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4512 q = 1) (hb : d73191 q = 1) : d69617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4513 q = 1) (hb : d73191 q = 1) : d69618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4514 q = 1) (hb : d73191 q = 1) : d69619 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58660 q = 1) (hb : d73191 q = 1) : d73267 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58660, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5107 (p : Pattern) (ha : d58666 p = 1) (hb : d73191 p = 1) : d73273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d73191 q = 1) : d73268 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5106 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d73191 q = 1) : d73269 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d73191 q = 1) : d73270 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d73191 q = 1) : d73271 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d73191 q = 1) : d73272 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d73191 q = 1) : d73273 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5108 (p : Pattern) (ha : d1629 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1629 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5109 (p : Pattern) (ha : d1639 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1635 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1636 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1637 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1638 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1639 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5110 (p : Pattern) (ha : d4539 p = 1) (hb : d73190 p = 1) : d69646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1814 q = 1) : d1814 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1815 q = 1) (hb : d58747 q = 1) : d5112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4530 q = 1) (hb : d73190 q = 1) : d69635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1821 q = 1) (hb : d73190 q = 1) : d1821 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4531 q = 1) (hb : d73190 q = 1) : d69636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4532 q = 1) (hb : d73190 q = 1) : d69644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4533 q = 1) (hb : d73190 q = 1) : d69645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4539 q = 1) (hb : d73190 q = 1) : d69646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5111 (p : Pattern) (ha : d4549 p = 1) (hb : d73190 p = 1) : d69656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1905 q = 1) : d1905 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1913 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1914 q = 1) (hb : d58747 q = 1) : d5170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d58747, d5170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1914, d58747, d5170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4545 q = 1) (hb : d73190 q = 1) : d69652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d73190, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4545, d73190, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1965 q = 1) (hb : d73190 q = 1) : d1965 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4546 q = 1) (hb : d73190 q = 1) : d69653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4546, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4547 q = 1) (hb : d73190 q = 1) : d69654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4548 q = 1) (hb : d73190 q = 1) : d69655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4549 q = 1) (hb : d73190 q = 1) : d69656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5112 (p : Pattern) (ha : d51766 p = 1) (hb : d73190 p = 1) : d73279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1657 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1658 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1659 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4525 q = 1) (hb : d73190 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1798 q = 1) (hb : d73190 q = 1) : d1798 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4526 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51764 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51764, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51765 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51765, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51766 q = 1) (hb : d73190 q = 1) : d73279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5113 (p : Pattern) (ha : d51769 p = 1) (hb : d73190 p = 1) : d73280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1657 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1658 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1659 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4525 q = 1) (hb : d73190 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1798 q = 1) (hb : d73190 q = 1) : d1798 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4526 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51764 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51764, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51765 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51765, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d1805 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1806 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1806, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d1807 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1808 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d1811 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1812 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d1813 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d1814 q = 1) : d1814 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d1815 q = 1) (hb : d58747 q = 1) : d5112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4530 q = 1) (hb : d73190 q = 1) : d69635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d1821 q = 1) (hb : d73190 q = 1) : d1821 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4531 q = 1) (hb : d73190 q = 1) : d69636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51767 q = 1) (hb : d73190 q = 1) : d69644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51767, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51768 q = 1) (hb : d73190 q = 1) : d69645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51768, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51769 q = 1) (hb : d73190 q = 1) : d73280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51769, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5114 (p : Pattern) (ha : d58674 p = 1) (hb : d73191 p = 1) : d73286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1631 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1640 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5108 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5109 q ha hb
  have h5 (q : Pattern) (ha : d1641 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1641, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1642 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51770 q = 1) (hb : d73190 q = 1) : d73281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5112 q ha hb
    | true =>
      simp only [d51770, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5113 q ha hb
  have h8 (q : Pattern) (ha : d58670 q = 1) (hb : d73191 q = 1) : d73282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58670, d73191, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58670, d73191, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58671 q = 1) (hb : d73191 q = 1) : d73283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58671, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58672 q = 1) (hb : d73191 q = 1) : d73284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58672, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4540 q = 1) (hb : d73190 q = 1) : d69647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5110 q ha hb
  have h13 (q : Pattern) (ha : d4541 q = 1) (hb : d73191 q = 1) : d69648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d73191, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4541, d73191, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4542 q = 1) (hb : d73191 q = 1) : d69649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4543 q = 1) (hb : d73191 q = 1) : d69650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58673 q = 1) (hb : d73191 q = 1) : d73285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58673, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d73190 q = 1) : d69657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5111 q ha hb
  have h18 (q : Pattern) (ha : d4551 q = 1) (hb : d73191 q = 1) : d69658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d73191, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4551, d73191, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4552 q = 1) (hb : d73191 q = 1) : d69659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4553 q = 1) (hb : d73191 q = 1) : d69660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4554 q = 1) (hb : d73191 q = 1) : d69661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58674 q = 1) (hb : d73191 q = 1) : d73286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58674, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5115 (p : Pattern) (ha : d58680 p = 1) (hb : d73191 p = 1) : d73292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d73191 q = 1) : d73287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5114 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d73191 q = 1) : d73288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d73191 q = 1) : d73289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d73191 q = 1) : d73290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d73191 q = 1) : d73291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d73191 q = 1) : d73292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5116 (p : Pattern) (ha : d2112 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2112 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5117 (p : Pattern) (ha : d2122 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2121 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2122 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5118 (p : Pattern) (ha : d4580 p = 1) (hb : d73190 p = 1) : d69689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2292 q = 1) : d2292 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2293 q = 1) (hb : d58747 q = 1) : d5229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4571 q = 1) (hb : d73190 q = 1) : d69678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2299 q = 1) (hb : d73190 q = 1) : d2299 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4572 q = 1) (hb : d73190 q = 1) : d69679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4573 q = 1) (hb : d73190 q = 1) : d69687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4574 q = 1) (hb : d73190 q = 1) : d69688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4580 q = 1) (hb : d73190 q = 1) : d69689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5119 (p : Pattern) (ha : d4590 p = 1) (hb : d73190 p = 1) : d69699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2383 q = 1) : d2383 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2391 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2392 q = 1) (hb : d58747 q = 1) : d5283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d58747, d5283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2392, d58747, d5283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4586 q = 1) (hb : d73190 q = 1) : d69695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d73190, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4586, d73190, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2443 q = 1) (hb : d73190 q = 1) : d2443 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4587 q = 1) (hb : d73190 q = 1) : d69696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4587, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4588 q = 1) (hb : d73190 q = 1) : d69697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4589 q = 1) (hb : d73190 q = 1) : d69698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4590 q = 1) (hb : d73190 q = 1) : d69699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5120 (p : Pattern) (ha : d51795 p = 1) (hb : d73190 p = 1) : d73299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2140 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2141 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2142 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4566 q = 1) (hb : d73190 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2276 q = 1) (hb : d73190 q = 1) : d2276 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4567 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51793 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51793, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51794 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51794, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51795 q = 1) (hb : d73190 q = 1) : d73299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro5121 (p : Pattern) (ha : d51798 p = 1) (hb : d73190 p = 1) : d73300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2140 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2141 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d2142 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4566 q = 1) (hb : d73190 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2276 q = 1) (hb : d73190 q = 1) : d2276 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4567 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51793 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51793, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51794 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51794, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d2283 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d2284 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2284, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d2285 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d2286 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d2289 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d2290 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d2291 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d2291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d2292 q = 1) : d2292 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d2293 q = 1) (hb : d58747 q = 1) : d5229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d4571 q = 1) (hb : d73190 q = 1) : d69678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h29 (q : Pattern) (ha : d2299 q = 1) (hb : d73190 q = 1) : d2299 q = 1 := by
    exact ha
  have h30 (q : Pattern) (ha : d4572 q = 1) (hb : d73190 q = 1) : d69679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d51796 q = 1) (hb : d73190 q = 1) : d69687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51796, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d51797 q = 1) (hb : d73190 q = 1) : d69688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51797, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d51798 q = 1) (hb : d73190 q = 1) : d73300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51798, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro5122 (p : Pattern) (ha : d58689 p = 1) (hb : d73191 p = 1) : d73306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5116 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2114 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2123 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5116 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5117 q ha hb
  have h5 (q : Pattern) (ha : d2124 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2124, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d2125 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51799 q = 1) (hb : d73190 q = 1) : d73301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5120 q ha hb
    | true =>
      simp only [d51799, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5121 q ha hb
  have h8 (q : Pattern) (ha : d58685 q = 1) (hb : d73191 q = 1) : d73302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58685, d73191, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58685, d73191, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58686 q = 1) (hb : d73191 q = 1) : d73303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58686, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58686, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58687 q = 1) (hb : d73191 q = 1) : d73304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58687, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58687, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4581 q = 1) (hb : d73190 q = 1) : d69690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5118 q ha hb
  have h13 (q : Pattern) (ha : d4582 q = 1) (hb : d73191 q = 1) : d69691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d73191, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4582, d73191, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4583 q = 1) (hb : d73191 q = 1) : d69692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4584 q = 1) (hb : d73191 q = 1) : d69693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58688 q = 1) (hb : d73191 q = 1) : d73305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58688, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58688, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4591 q = 1) (hb : d73190 q = 1) : d69700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5119 q ha hb
  have h18 (q : Pattern) (ha : d4592 q = 1) (hb : d73191 q = 1) : d69701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d73191, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4592, d73191, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4593 q = 1) (hb : d73191 q = 1) : d69702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4594 q = 1) (hb : d73191 q = 1) : d69703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4595 q = 1) (hb : d73191 q = 1) : d69704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58689 q = 1) (hb : d73191 q = 1) : d73306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58689, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58689, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro5123 (p : Pattern) (ha : d58695 p = 1) (hb : d73191 p = 1) : d73312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58690 q = 1) (hb : d73191 q = 1) : d73307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58690, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58690, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5122 q ha hb
  have h2 (q : Pattern) (ha : d58691 q = 1) (hb : d73191 q = 1) : d73308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58691, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58691, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58692 q = 1) (hb : d73191 q = 1) : d73309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58692, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58692, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58693 q = 1) (hb : d73191 q = 1) : d73310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58693, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58693, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58694 q = 1) (hb : d73191 q = 1) : d73311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58694, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58694, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58695 q = 1) (hb : d73191 q = 1) : d73312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58695, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58695, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5124 (p : Pattern) (ha : d58701 p = 1) (hb : d73191 p = 1) : d73318 p = 1 := by
  have h0 (q : Pattern) (ha : d58642 q = 1) (hb : d73191 q = 1) : d73239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58642, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5083 q ha hb
    | true =>
      simp only [d58642, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5091 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58654 q = 1) (hb : d73191 q = 1) : d73256 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58654, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58654, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5099 q ha hb
  have h3 (q : Pattern) (ha : d58655 q = 1) (hb : d73191 q = 1) : d73257 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58655, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58655, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58667 q = 1) (hb : d73191 q = 1) : d73274 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58667, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58667, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5107 q ha hb
  have h5 (q : Pattern) (ha : d58668 q = 1) (hb : d73191 q = 1) : d73275 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58668, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58668, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58669 q = 1) (hb : d73191 q = 1) : d73276 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58669, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58669, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58681 q = 1) (hb : d73191 q = 1) : d73293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58681, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58681, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5115 q ha hb
  have h8 (q : Pattern) (ha : d58682 q = 1) (hb : d73191 q = 1) : d73294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58682, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58682, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58683 q = 1) (hb : d73191 q = 1) : d73295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58683, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58683, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58684 q = 1) (hb : d73191 q = 1) : d73296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58684, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58684, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58696 q = 1) (hb : d73191 q = 1) : d73313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58696, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58696, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5123 q ha hb
  have h12 (q : Pattern) (ha : d58697 q = 1) (hb : d73191 q = 1) : d73314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58697, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58697, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d58698 q = 1) (hb : d73191 q = 1) : d73315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d58698, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58698, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d58699 q = 1) (hb : d73191 q = 1) : d73316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d58699, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58699, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d58700 q = 1) (hb : d73191 q = 1) : d73317 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d58700, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d58700, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d58701 q = 1) (hb : d73191 q = 1) : d73318 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d58701, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d58701, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5125 (p : Pattern) (ha : d58707 p = 1) (hb : d73191 p = 1) : d73324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58702 q = 1) (hb : d73191 q = 1) : d73319 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d58702, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5124 q ha hb
    | true =>
      simp only [d58702, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58703 q = 1) (hb : d73191 q = 1) : d73320 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d58703, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58703, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58704 q = 1) (hb : d73191 q = 1) : d73321 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d58704, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58704, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58705 q = 1) (hb : d73191 q = 1) : d73322 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d58705, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58705, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58706 q = 1) (hb : d73191 q = 1) : d73323 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d58706, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58706, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58707 q = 1) (hb : d73191 q = 1) : d73324 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d58707, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58707, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5126 (p : Pattern) (ha : d58713 p = 1) (hb : d73191 p = 1) : d73330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58708 q = 1) (hb : d73191 q = 1) : d73325 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d58708, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5125 q ha hb
    | true =>
      simp only [d58708, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58709 q = 1) (hb : d73191 q = 1) : d73326 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d58709, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58709, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58710 q = 1) (hb : d73191 q = 1) : d73327 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d58710, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58710, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58711 q = 1) (hb : d73191 q = 1) : d73328 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d58711, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58711, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58712 q = 1) (hb : d73191 q = 1) : d73329 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d58712, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58712, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58713 q = 1) (hb : d73191 q = 1) : d73330 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d58713, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58713, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5127 (p : Pattern) (ha : d58719 p = 1) (hb : d73191 p = 1) : d73336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58714 q = 1) (hb : d73191 q = 1) : d73331 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d58714, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5126 q ha hb
    | true =>
      simp only [d58714, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58715 q = 1) (hb : d73191 q = 1) : d73332 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d58715, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58715, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58716 q = 1) (hb : d73191 q = 1) : d73333 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d58716, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58716, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58717 q = 1) (hb : d73191 q = 1) : d73334 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d58717, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58717, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58718 q = 1) (hb : d73191 q = 1) : d73335 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d58718, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58718, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58719 q = 1) (hb : d73191 q = 1) : d73336 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d58719, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58719, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5128 (p : Pattern) (ha : d58725 p = 1) (hb : d73191 p = 1) : d73342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58720 q = 1) (hb : d73191 q = 1) : d73337 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d58720, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5127 q ha hb
    | true =>
      simp only [d58720, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58721 q = 1) (hb : d73191 q = 1) : d73338 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d58721, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58721, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58722 q = 1) (hb : d73191 q = 1) : d73339 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d58722, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58722, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58723 q = 1) (hb : d73191 q = 1) : d73340 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d58723, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58723, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58724 q = 1) (hb : d73191 q = 1) : d73341 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d58724, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58724, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58725 q = 1) (hb : d73191 q = 1) : d73342 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d58725, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58725, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5129 (p : Pattern) (ha : d58731 p = 1) (hb : d73191 p = 1) : d73348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58726 q = 1) (hb : d73191 q = 1) : d73343 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d58726, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5128 q ha hb
    | true =>
      simp only [d58726, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58727 q = 1) (hb : d73191 q = 1) : d73344 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d58727, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58727, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58728 q = 1) (hb : d73191 q = 1) : d73345 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d58728, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58728, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58729 q = 1) (hb : d73191 q = 1) : d73346 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d58729, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58729, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58730 q = 1) (hb : d73191 q = 1) : d73347 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d58730, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58730, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58731 q = 1) (hb : d73191 q = 1) : d73348 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d58731, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58731, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5130 (p : Pattern) (ha : d58737 p = 1) (hb : d73191 p = 1) : d73354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58732 q = 1) (hb : d73191 q = 1) : d73349 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d58732, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5129 q ha hb
    | true =>
      simp only [d58732, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58733 q = 1) (hb : d73191 q = 1) : d73350 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d58733, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58733, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58734 q = 1) (hb : d73191 q = 1) : d73351 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d58734, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58734, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58735 q = 1) (hb : d73191 q = 1) : d73352 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d58735, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58735, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58736 q = 1) (hb : d73191 q = 1) : d73353 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d58736, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58736, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58737 q = 1) (hb : d73191 q = 1) : d73354 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58737, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5131 (p : Pattern) (ha : d58743 p = 1) (hb : d73191 p = 1) : d73360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58738 q = 1) (hb : d73191 q = 1) : d73355 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5130 q ha hb
    | true =>
      simp only [d58738, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d58739 q = 1) (hb : d73191 q = 1) : d73356 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58740 q = 1) (hb : d73191 q = 1) : d73357 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d58741 q = 1) (hb : d73191 q = 1) : d73358 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d58742 q = 1) (hb : d73191 q = 1) : d73359 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d58743 q = 1) (hb : d73191 q = 1) : d73360 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d58743, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d58743, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5132 (p : Pattern) (ha : d68228 p = 1) (hb : d73194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d371 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d371, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68225 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68225, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68225, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68226 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68227 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68228 q = 1) (hb : d73194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68228, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68228, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5133 (p : Pattern) (ha : d68233 p = 1) (hb : d73195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d371 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d371, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68225 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68225, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68225, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68226 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68227 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d390 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d391 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d391, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68230 q = 1) (hb : d69437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68230, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d68230, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68231 q = 1) (hb : d69445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68231, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68231, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68232 q = 1) (hb : d69446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68232, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68232, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68233 q = 1) (hb : d73195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68233, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68233, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5134 (p : Pattern) (ha : d68238 p = 1) (hb : d69447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d391 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d391, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h6 (q : Pattern) (ha : d68230 q = 1) (hb : d69437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68230, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68230, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68231 q = 1) (hb : d69445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68231, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68231, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68232 q = 1) (hb : d69446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68232, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68232, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68238 q = 1) (hb : d69447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68238, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68238, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5135 (p : Pattern) (ha : d68248 p = 1) (hb : d69456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d451, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d452 q = 1) (hb : d68244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d452, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
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
  have h6 (q : Pattern) (ha : d68245 q = 1) (hb : d69453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68245, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68245, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68246 q = 1) (hb : d69454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68246, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68246, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68247 q = 1) (hb : d69455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68247, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68247, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68248 q = 1) (hb : d69456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68248, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68248, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5136 (p : Pattern) (ha : d68254 p = 1) (hb : d73201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68234 q = 1) (hb : d73196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68234, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5132 q ha hb
    | true =>
      simp only [d68234, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5133 q ha hb
  have h2 (q : Pattern) (ha : d68235 q = 1) (hb : d73197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68235, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68235, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68236 q = 1) (hb : d73198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68236, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68236, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68237 q = 1) (hb : d73199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68237, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68237, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68239 q = 1) (hb : d69448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68239, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68239, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5134 q ha hb
  have h6 (q : Pattern) (ha : d68240 q = 1) (hb : d69449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68240, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68240, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68241 q = 1) (hb : d69450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68241, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68241, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68242 q = 1) (hb : d69451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68242, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68242, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68243 q = 1) (hb : d73200 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68243, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68243, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68249 q = 1) (hb : d69457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68249, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68249, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5135 q ha hb
  have h11 (q : Pattern) (ha : d68250 q = 1) (hb : d69458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68250, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68250, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68251 q = 1) (hb : d69459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68251, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68251, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68252 q = 1) (hb : d69460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68252, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68252, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68253 q = 1) (hb : d69461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68253, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68253, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68254 q = 1) (hb : d73201 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68254, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68254, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5137 (p : Pattern) (ha : d68264 p = 1) (hb : d73209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4711 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68260 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68260, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68260, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68261 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68261, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68261, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68262 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68263 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68264 q = 1) (hb : d73209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68264, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68264, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5138 (p : Pattern) (ha : d68269 p = 1) (hb : d73210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4711 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68260 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68260, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68260, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68261 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68261, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68261, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68262 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68263 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4725 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68265 q = 1) (hb : d69473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68265, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68265, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68266 q = 1) (hb : d69474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68266, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68266, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68267 q = 1) (hb : d69482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68267, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68267, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68268 q = 1) (hb : d69483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68268, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68268, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68269 q = 1) (hb : d73210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68269, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68269, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5139 (p : Pattern) (ha : d68274 p = 1) (hb : d69484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4725 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d4725, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68265 q = 1) (hb : d69473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68265, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68265, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68266 q = 1) (hb : d69474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68266, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68266, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68267 q = 1) (hb : d69482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68267, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68267, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68268 q = 1) (hb : d69483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68268, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68268, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68274 q = 1) (hb : d69484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68274, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68274, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5140 (p : Pattern) (ha : d68284 p = 1) (hb : d69494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4755 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4755, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49 q ha hb
    | true =>
      simp only [d4755, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68280 q = 1) (hb : d69490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68280, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68280, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d451 q = 1) (hb : d52198 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d451, d52198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d452 q = 1) (hb : d52199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d452, d52199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68281 q = 1) (hb : d69491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68281, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68281, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68282 q = 1) (hb : d69492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68282, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68282, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68283 q = 1) (hb : d69493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68283, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68283, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68284 q = 1) (hb : d69494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68284, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68284, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5141 (p : Pattern) (ha : d68290 p = 1) (hb : d73216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68270 q = 1) (hb : d73211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68270, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5137 q ha hb
    | true =>
      simp only [d68270, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5138 q ha hb
  have h2 (q : Pattern) (ha : d68271 q = 1) (hb : d73212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68271, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68271, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68272 q = 1) (hb : d73213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68272, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68272, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68273 q = 1) (hb : d73214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68273, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68273, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68275 q = 1) (hb : d69485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68275, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68275, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5139 q ha hb
  have h6 (q : Pattern) (ha : d68276 q = 1) (hb : d69486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68276, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68276, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68277 q = 1) (hb : d69487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68277, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68277, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68278 q = 1) (hb : d69488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68278, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68278, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68279 q = 1) (hb : d73215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68279, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68279, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68285 q = 1) (hb : d69495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68285, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68285, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5140 q ha hb
  have h11 (q : Pattern) (ha : d68286 q = 1) (hb : d69496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68286, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68286, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68287 q = 1) (hb : d69497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68287, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68287, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68288 q = 1) (hb : d69498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68288, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68288, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68289 q = 1) (hb : d69499 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68289, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68289, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68290 q = 1) (hb : d73216 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68290, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68290, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5142 (p : Pattern) (ha : d68296 p = 1) (hb : d73222 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d68255 q = 1) (hb : d73202 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68255, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68255, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5136 q ha hb
  have h6 (q : Pattern) (ha : d68256 q = 1) (hb : d73203 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68256, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68256, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68257 q = 1) (hb : d73204 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68257, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68257, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68258 q = 1) (hb : d73205 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68258, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68258, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68259 q = 1) (hb : d73206 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68259, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68259, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68291 q = 1) (hb : d73217 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68291, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68291, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5141 q ha hb
  have h11 (q : Pattern) (ha : d68292 q = 1) (hb : d73218 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68292, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68292, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68293 q = 1) (hb : d73219 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68293, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68293, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68294 q = 1) (hb : d73220 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68294, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68294, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68295 q = 1) (hb : d73221 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68295, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68295, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68296 q = 1) (hb : d73222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68296, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68296, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5143 (p : Pattern) (ha : d68301 p = 1) (hb : d73225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4796 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68297 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68297, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68297, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68298 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68298, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68298, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68299 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68300 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68301 q = 1) (hb : d73225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68301, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68301, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5144 (p : Pattern) (ha : d68306 p = 1) (hb : d73226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4796 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68297 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68297, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68297, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68298 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68298, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68298, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68299 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68300 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4810 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68302 q = 1) (hb : d69512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68302, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68302, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68303 q = 1) (hb : d69513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68303, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68303, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68304 q = 1) (hb : d69521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68304, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68304, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68305 q = 1) (hb : d69522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68305, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68305, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68306 q = 1) (hb : d73226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68306, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68306, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5145 (p : Pattern) (ha : d68311 p = 1) (hb : d69523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4810 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d4810, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68302 q = 1) (hb : d69512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68302, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68302, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68303 q = 1) (hb : d69513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68303, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68303, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68304 q = 1) (hb : d69521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68304, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68304, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68305 q = 1) (hb : d69522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68305, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68305, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68311 q = 1) (hb : d69523 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68311, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68311, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5146 (p : Pattern) (ha : d68321 p = 1) (hb : d69533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4849 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4849, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro84 q ha hb
    | true =>
      simp only [d4849, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68317 q = 1) (hb : d69529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68317, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68317, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d720 q = 1) (hb : d52401 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85 q ha hb
    | true =>
      simp only [d720, d52401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d721 q = 1) (hb : d52402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d721, d52402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68318 q = 1) (hb : d69530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68318, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68318, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68319 q = 1) (hb : d69531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68319, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68319, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68320 q = 1) (hb : d69532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68320, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68320, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68321 q = 1) (hb : d69533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68321, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68321, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5147 (p : Pattern) (ha : d68327 p = 1) (hb : d73232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68307 q = 1) (hb : d73227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68307, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5143 q ha hb
    | true =>
      simp only [d68307, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5144 q ha hb
  have h2 (q : Pattern) (ha : d68308 q = 1) (hb : d73228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68308, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68308, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68309 q = 1) (hb : d73229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68309, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68309, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68310 q = 1) (hb : d73230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68310, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68310, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68312 q = 1) (hb : d69524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68312, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68312, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5145 q ha hb
  have h6 (q : Pattern) (ha : d68313 q = 1) (hb : d69525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68313, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68313, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68314 q = 1) (hb : d69526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68314, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68314, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68315 q = 1) (hb : d69527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68315, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68315, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68316 q = 1) (hb : d73231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68316, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68316, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68322 q = 1) (hb : d69534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68322, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68322, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5146 q ha hb
  have h11 (q : Pattern) (ha : d68323 q = 1) (hb : d69535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68323, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68323, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68324 q = 1) (hb : d69536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68324, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68324, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68325 q = 1) (hb : d69537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68325, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68325, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68326 q = 1) (hb : d69538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68326, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68326, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68327 q = 1) (hb : d73232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68327, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68327, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5148 (p : Pattern) (ha : d68333 p = 1) (hb : d73238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68328 q = 1) (hb : d73233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68328, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68328, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5147 q ha hb
  have h2 (q : Pattern) (ha : d68329 q = 1) (hb : d73234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68329, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68329, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68330 q = 1) (hb : d73235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68330, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68330, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68331 q = 1) (hb : d73236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68331, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68331, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68332 q = 1) (hb : d73237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68332, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68332, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68333 q = 1) (hb : d73238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68333, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68333, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5149 (p : Pattern) (ha : d68339 p = 1) (hb : d73242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4891 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68335 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68335, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68335, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68336 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68336, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68336, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68337 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68338 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68339 q = 1) (hb : d73242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68339, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68339, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5150 (p : Pattern) (ha : d68344 p = 1) (hb : d73243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4891 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68335 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68335, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68335, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68336 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68336, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68336, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68337 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68338 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4905 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68340 q = 1) (hb : d69552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68340, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68340, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68341 q = 1) (hb : d69553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68341, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68341, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68342 q = 1) (hb : d69561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68342, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68342, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68343 q = 1) (hb : d69562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68343, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68343, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68344 q = 1) (hb : d73243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68344, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68344, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5151 (p : Pattern) (ha : d68349 p = 1) (hb : d69563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4905 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d4905, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68340 q = 1) (hb : d69552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68340, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68340, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68341 q = 1) (hb : d69553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68341, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68341, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68342 q = 1) (hb : d69561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68342, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68342, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68343 q = 1) (hb : d69562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68343, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68343, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68349 q = 1) (hb : d69563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68349, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68349, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5152 (p : Pattern) (ha : d68359 p = 1) (hb : d69573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4944 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4944, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro131 q ha hb
    | true =>
      simp only [d4944, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68355 q = 1) (hb : d69569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68355, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68355, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1053 q = 1) (hb : d52638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q ha hb
    | true =>
      simp only [d1053, d52638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1054 q = 1) (hb : d52639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1054, d52639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68356 q = 1) (hb : d69570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68356, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68356, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68357 q = 1) (hb : d69571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68357, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68357, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68358 q = 1) (hb : d69572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68358, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68358, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68359 q = 1) (hb : d69573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68359, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68359, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5153 (p : Pattern) (ha : d68365 p = 1) (hb : d73249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68345 q = 1) (hb : d73244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68345, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5149 q ha hb
    | true =>
      simp only [d68345, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5150 q ha hb
  have h2 (q : Pattern) (ha : d68346 q = 1) (hb : d73245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68346, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68346, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68347 q = 1) (hb : d73246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68347, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68347, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68348 q = 1) (hb : d73247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68348, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68348, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68350 q = 1) (hb : d69564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68350, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68350, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5151 q ha hb
  have h6 (q : Pattern) (ha : d68351 q = 1) (hb : d69565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68351, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68351, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68352 q = 1) (hb : d69566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68352, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68352, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68353 q = 1) (hb : d69567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68353, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68353, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68354 q = 1) (hb : d73248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68354, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68354, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68360 q = 1) (hb : d69574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68360, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68360, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5152 q ha hb
  have h11 (q : Pattern) (ha : d68361 q = 1) (hb : d69575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68361, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68361, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68362 q = 1) (hb : d69576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68362, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68362, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68363 q = 1) (hb : d69577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68363, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68363, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68364 q = 1) (hb : d69578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68364, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68364, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68365 q = 1) (hb : d73249 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68365, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68365, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5154 (p : Pattern) (ha : d68371 p = 1) (hb : d73255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68366 q = 1) (hb : d73250 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68366, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68366, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5153 q ha hb
  have h2 (q : Pattern) (ha : d68367 q = 1) (hb : d73251 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68367, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68367, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68368 q = 1) (hb : d73252 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68368, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68368, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68369 q = 1) (hb : d73253 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68369, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68369, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68370 q = 1) (hb : d73254 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68370, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68370, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68371 q = 1) (hb : d73255 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68371, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68371, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5155 (p : Pattern) (ha : d68378 p = 1) (hb : d73260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4987 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68374 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68374, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68374, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68375 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68375, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68375, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68376 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68377 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68378 q = 1) (hb : d73260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68378, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68378, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5156 (p : Pattern) (ha : d68383 p = 1) (hb : d73261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4987 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68374 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68374, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68374, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68375 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68375, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68375, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68376 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68377 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5001 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68379 q = 1) (hb : d69593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68379, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68379, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68380 q = 1) (hb : d69594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68380, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68380, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68381 q = 1) (hb : d69602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68381, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68381, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68382 q = 1) (hb : d69603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68382, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68382, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68383 q = 1) (hb : d73261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68383, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68383, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5157 (p : Pattern) (ha : d68388 p = 1) (hb : d69604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5001 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d5001, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68379 q = 1) (hb : d69593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68379, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68379, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68380 q = 1) (hb : d69594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68380, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68380, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68381 q = 1) (hb : d69602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68381, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68381, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68382 q = 1) (hb : d69603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68382, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68382, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68388 q = 1) (hb : d69604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68388, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68388, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5158 (p : Pattern) (ha : d68398 p = 1) (hb : d69614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5054 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5054, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro183 q ha hb
    | true =>
      simp only [d5054, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68394 q = 1) (hb : d69610 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68394, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68394, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1487 q = 1) (hb : d52932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q ha hb
    | true =>
      simp only [d1487, d52932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1488 q = 1) (hb : d52933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1488, d52933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68395 q = 1) (hb : d69611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68395, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68395, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68396 q = 1) (hb : d69612 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68396, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68396, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68397 q = 1) (hb : d69613 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68397, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68397, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68398 q = 1) (hb : d69614 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68398, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68398, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5159 (p : Pattern) (ha : d68404 p = 1) (hb : d73267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68384 q = 1) (hb : d73262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68384, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5155 q ha hb
    | true =>
      simp only [d68384, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5156 q ha hb
  have h2 (q : Pattern) (ha : d68385 q = 1) (hb : d73263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68385, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68385, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68386 q = 1) (hb : d73264 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68386, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68386, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68387 q = 1) (hb : d73265 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68387, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68387, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68389 q = 1) (hb : d69605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68389, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68389, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5157 q ha hb
  have h6 (q : Pattern) (ha : d68390 q = 1) (hb : d69606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68390, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68390, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68391 q = 1) (hb : d69607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68391, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68391, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68392 q = 1) (hb : d69608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68392, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68392, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68393 q = 1) (hb : d73266 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68393, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68393, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68399 q = 1) (hb : d69615 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68399, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68399, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5158 q ha hb
  have h11 (q : Pattern) (ha : d68400 q = 1) (hb : d69616 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68400, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68400, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68401 q = 1) (hb : d69617 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68401, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68401, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68402 q = 1) (hb : d69618 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68402, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68402, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68403 q = 1) (hb : d69619 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68403, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68403, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68404 q = 1) (hb : d73267 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68404, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68404, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5160 (p : Pattern) (ha : d68410 p = 1) (hb : d73273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68405 q = 1) (hb : d73268 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68405, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68405, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5159 q ha hb
  have h2 (q : Pattern) (ha : d68406 q = 1) (hb : d73269 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68406, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68406, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68407 q = 1) (hb : d73270 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68407, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68407, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68408 q = 1) (hb : d73271 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68408, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68408, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68409 q = 1) (hb : d73272 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68409, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68409, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68410 q = 1) (hb : d73273 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68410, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68410, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5161 (p : Pattern) (ha : d68418 p = 1) (hb : d73279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5098 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68414 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68414, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68414, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68415 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68415, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68415, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68416 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68417 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68418 q = 1) (hb : d73279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68418, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68418, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5162 (p : Pattern) (ha : d68423 p = 1) (hb : d73280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5098 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68414 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68414, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68414, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68415 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68415, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68415, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68416 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68417 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5112 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68419 q = 1) (hb : d69635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68419, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68419, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68420 q = 1) (hb : d69636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68420, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68420, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68421 q = 1) (hb : d69644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68421, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68421, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68422 q = 1) (hb : d69645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68422, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68422, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68423 q = 1) (hb : d73280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68423, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68423, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5163 (p : Pattern) (ha : d68428 p = 1) (hb : d69646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5112 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d5112, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68419 q = 1) (hb : d69635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68419, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68419, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68420 q = 1) (hb : d69636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68420, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68420, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68421 q = 1) (hb : d69644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68421, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68421, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68422 q = 1) (hb : d69645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68422, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68422, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68428 q = 1) (hb : d69646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68428, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68428, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5164 (p : Pattern) (ha : d68438 p = 1) (hb : d69656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5170 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5170, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro239 q ha hb
    | true =>
      simp only [d5170, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68434 q = 1) (hb : d69652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68434, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68434, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d1964 q = 1) (hb : d53247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q ha hb
    | true =>
      simp only [d1964, d53247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1965 q = 1) (hb : d53248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1965, d53248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68435 q = 1) (hb : d69653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68435, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68435, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68436 q = 1) (hb : d69654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68436, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68436, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68437 q = 1) (hb : d69655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68437, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68437, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68438 q = 1) (hb : d69656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68438, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68438, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5165 (p : Pattern) (ha : d68444 p = 1) (hb : d73286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68424 q = 1) (hb : d73281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68424, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5161 q ha hb
    | true =>
      simp only [d68424, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5162 q ha hb
  have h2 (q : Pattern) (ha : d68425 q = 1) (hb : d73282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68425, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68425, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68426 q = 1) (hb : d73283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68426, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68426, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68427 q = 1) (hb : d73284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68427, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68427, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68429 q = 1) (hb : d69647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68429, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68429, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5163 q ha hb
  have h6 (q : Pattern) (ha : d68430 q = 1) (hb : d69648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68430, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68430, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68431 q = 1) (hb : d69649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68431, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68431, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68432 q = 1) (hb : d69650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68432, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68432, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68433 q = 1) (hb : d73285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68433, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68433, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68439 q = 1) (hb : d69657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68439, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68439, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5164 q ha hb
  have h11 (q : Pattern) (ha : d68440 q = 1) (hb : d69658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68440, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68440, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68441 q = 1) (hb : d69659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68441, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68441, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68442 q = 1) (hb : d69660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68442, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68442, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68443 q = 1) (hb : d69661 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68443, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68443, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68444 q = 1) (hb : d73286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68444, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68444, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5166 (p : Pattern) (ha : d68450 p = 1) (hb : d73292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68445 q = 1) (hb : d73287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68445, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68445, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5165 q ha hb
  have h2 (q : Pattern) (ha : d68446 q = 1) (hb : d73288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68446, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68446, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68447 q = 1) (hb : d73289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68447, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68447, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68448 q = 1) (hb : d73290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68448, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68448, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68449 q = 1) (hb : d73291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68449, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68449, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68450 q = 1) (hb : d73292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68450, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68450, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5167 (p : Pattern) (ha : d68459 p = 1) (hb : d73299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5215 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68455 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68455, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68455, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68456 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68456, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68456, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68457 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68458 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68459 q = 1) (hb : d73299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68459, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68459, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5168 (p : Pattern) (ha : d68464 p = 1) (hb : d73300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5215 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68455 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68455, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68455, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68456 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68456, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68456, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68457 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68458 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5229 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68460 q = 1) (hb : d69678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68460, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68460, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d68461 q = 1) (hb : d69679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68461, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68461, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d68462 q = 1) (hb : d69687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68462, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68462, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68463 q = 1) (hb : d69688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68463, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68463, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68464 q = 1) (hb : d73300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68464, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68464, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5169 (p : Pattern) (ha : d68469 p = 1) (hb : d69689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5229 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d5229, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68460 q = 1) (hb : d69678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68460, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68460, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68461 q = 1) (hb : d69679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68461, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68461, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68462 q = 1) (hb : d69687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68462, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68462, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68463 q = 1) (hb : d69688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68463, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68463, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68469 q = 1) (hb : d69689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68469, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68469, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5170 (p : Pattern) (ha : d68479 p = 1) (hb : d69699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5283 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5283, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro298 q ha hb
    | true =>
      simp only [d5283, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68475 q = 1) (hb : d69695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68475, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68475, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d2442 q = 1) (hb : d53564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q ha hb
    | true =>
      simp only [d2442, d53564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2443 q = 1) (hb : d53565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2443, d53565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d68476 q = 1) (hb : d69696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68476, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68476, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68477 q = 1) (hb : d69697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68477, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68477, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68478 q = 1) (hb : d69698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68478, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68478, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68479 q = 1) (hb : d69699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68479, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68479, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro5171 (p : Pattern) (ha : d68485 p = 1) (hb : d73306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68465 q = 1) (hb : d73301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68465, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5167 q ha hb
    | true =>
      simp only [d68465, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5168 q ha hb
  have h2 (q : Pattern) (ha : d68466 q = 1) (hb : d73302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68466, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68466, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68467 q = 1) (hb : d73303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68467, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68467, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68468 q = 1) (hb : d73304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68468, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68468, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68470 q = 1) (hb : d69690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68470, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68470, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5169 q ha hb
  have h6 (q : Pattern) (ha : d68471 q = 1) (hb : d69691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68471, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68471, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68472 q = 1) (hb : d69692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68472, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68472, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68473 q = 1) (hb : d69693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68473, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68473, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68474 q = 1) (hb : d73305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68474, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68474, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68480 q = 1) (hb : d69700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68480, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68480, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5170 q ha hb
  have h11 (q : Pattern) (ha : d68481 q = 1) (hb : d69701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68481, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68481, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68482 q = 1) (hb : d69702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68482, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68482, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68483 q = 1) (hb : d69703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68483, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68483, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68484 q = 1) (hb : d69704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68484, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68484, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68485 q = 1) (hb : d73306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68485, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68485, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5172 (p : Pattern) (ha : d68491 p = 1) (hb : d73312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68486 q = 1) (hb : d73307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68486, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68486, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5171 q ha hb
  have h2 (q : Pattern) (ha : d68487 q = 1) (hb : d73308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68487, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68487, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68488 q = 1) (hb : d73309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68488, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68488, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68489 q = 1) (hb : d73310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68489, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68489, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68490 q = 1) (hb : d73311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68490, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68490, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68491 q = 1) (hb : d73312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68491, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68491, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5173 (p : Pattern) (ha : d68497 p = 1) (hb : d73318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68334 q = 1) (hb : d73239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68334, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5142 q ha hb
    | true =>
      simp only [d68334, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68372 q = 1) (hb : d73256 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68372, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68372, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5154 q ha hb
  have h3 (q : Pattern) (ha : d68373 q = 1) (hb : d73257 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68373, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d68373, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68411 q = 1) (hb : d73274 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68411, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68411, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5160 q ha hb
  have h5 (q : Pattern) (ha : d68412 q = 1) (hb : d73275 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68412, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68412, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68413 q = 1) (hb : d73276 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68413, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68413, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68451 q = 1) (hb : d73293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68451, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68451, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5166 q ha hb
  have h8 (q : Pattern) (ha : d68452 q = 1) (hb : d73294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68452, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68452, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68453 q = 1) (hb : d73295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68453, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68453, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68454 q = 1) (hb : d73296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68454, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68454, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68492 q = 1) (hb : d73313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68492, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68492, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5172 q ha hb
  have h12 (q : Pattern) (ha : d68493 q = 1) (hb : d73314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68493, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68493, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68494 q = 1) (hb : d73315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68494, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68494, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68495 q = 1) (hb : d73316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68495, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68495, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68496 q = 1) (hb : d73317 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d68496, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68496, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68497 q = 1) (hb : d73318 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d68497, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68497, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5174 (p : Pattern) (ha : d68503 p = 1) (hb : d73324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68498 q = 1) (hb : d73319 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d68498, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5173 q ha hb
    | true =>
      simp only [d68498, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68499 q = 1) (hb : d73320 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d68499, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68499, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68500 q = 1) (hb : d73321 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d68500, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68500, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68501 q = 1) (hb : d73322 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d68501, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68501, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68502 q = 1) (hb : d73323 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d68502, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68502, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68503 q = 1) (hb : d73324 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d68503, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68503, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5175 (p : Pattern) (ha : d68509 p = 1) (hb : d73330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68504 q = 1) (hb : d73325 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d68504, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5174 q ha hb
    | true =>
      simp only [d68504, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68505 q = 1) (hb : d73326 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d68505, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68505, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68506 q = 1) (hb : d73327 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d68506, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68506, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68507 q = 1) (hb : d73328 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d68507, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68507, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68508 q = 1) (hb : d73329 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d68508, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68508, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68509 q = 1) (hb : d73330 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d68509, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68509, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5176 (p : Pattern) (ha : d68515 p = 1) (hb : d73336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68510 q = 1) (hb : d73331 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d68510, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5175 q ha hb
    | true =>
      simp only [d68510, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68511 q = 1) (hb : d73332 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d68511, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68511, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68512 q = 1) (hb : d73333 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d68512, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68512, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68513 q = 1) (hb : d73334 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d68513, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68513, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68514 q = 1) (hb : d73335 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d68514, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68514, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68515 q = 1) (hb : d73336 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d68515, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68515, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5177 (p : Pattern) (ha : d68521 p = 1) (hb : d73342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68516 q = 1) (hb : d73337 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d68516, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5176 q ha hb
    | true =>
      simp only [d68516, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68517 q = 1) (hb : d73338 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d68517, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68517, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68518 q = 1) (hb : d73339 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d68518, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68518, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68519 q = 1) (hb : d73340 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d68519, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68519, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68520 q = 1) (hb : d73341 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d68520, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68520, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68521 q = 1) (hb : d73342 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d68521, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68521, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5178 (p : Pattern) (ha : d68527 p = 1) (hb : d73348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68522 q = 1) (hb : d73343 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d68522, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5177 q ha hb
    | true =>
      simp only [d68522, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68523 q = 1) (hb : d73344 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d68523, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68523, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68524 q = 1) (hb : d73345 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d68524, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68524, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68525 q = 1) (hb : d73346 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d68525, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68525, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68526 q = 1) (hb : d73347 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d68526, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68526, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68527 q = 1) (hb : d73348 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d68527, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68527, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5179 (p : Pattern) (ha : d68533 p = 1) (hb : d73354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68528 q = 1) (hb : d73349 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d68528, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5178 q ha hb
    | true =>
      simp only [d68528, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68529 q = 1) (hb : d73350 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d68529, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68529, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68530 q = 1) (hb : d73351 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d68530, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68530, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68531 q = 1) (hb : d73352 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d68531, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68531, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68532 q = 1) (hb : d73353 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d68532, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68532, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68533 q = 1) (hb : d73354 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d68533, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68533, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5180 (p : Pattern) (ha : d68539 p = 1) (hb : d73360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68534 q = 1) (hb : d73355 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d68534, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5179 q ha hb
    | true =>
      simp only [d68534, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68535 q = 1) (hb : d73356 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d68535, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68535, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68536 q = 1) (hb : d73357 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d68536, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68536, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68537 q = 1) (hb : d73358 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d68537, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68537, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68538 q = 1) (hb : d73359 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d68538, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68538, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68539 q = 1) (hb : d73360 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d68539, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68539, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5181 (p : Pattern) (ha : d406 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5182 (p : Pattern) (ha : d462 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5183 (p : Pattern) (ha : d53647 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5069 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5070 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53637 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53638 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5181 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5182 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5184 (p : Pattern) (ha : d53655 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5185 (p : Pattern) (ha : d53665 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53661, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5186 (p : Pattern) (ha : d53671 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5076 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5077 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53653 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53654 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53656 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5184 q ha hb
  have h8 (q : Pattern) (ha : d53657 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53657, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53658 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53659 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53660 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53666 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5185 q ha hb
  have h13 (q : Pattern) (ha : d53667 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53667, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53668 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53669 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53670 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53671 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5187 (p : Pattern) (ha : d53677 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5183 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5186 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5188 (p : Pattern) (ha : d53680 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d504 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d505 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d506 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53680 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5189 (p : Pattern) (ha : d53691 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53687 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53687, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53688 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53689 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53690 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53691 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5190 (p : Pattern) (ha : d53697 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5084 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d509 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53678 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53679 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53681 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5188 q ha hb
  have h8 (q : Pattern) (ha : d53682 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53682, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53683 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53684 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53685 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53692 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5189 q ha hb
  have h13 (q : Pattern) (ha : d53693 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53693, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53694 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53695 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53696 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53697 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5191 (p : Pattern) (ha : d53703 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5190 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5192 (p : Pattern) (ha : d53707 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d796 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d797 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d798 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53707 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5193 (p : Pattern) (ha : d53718 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53714 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53714, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53715 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53716 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53717 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53718 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5194 (p : Pattern) (ha : d53724 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5092 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5093 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d801 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53705 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53706 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53708 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5192 q ha hb
  have h8 (q : Pattern) (ha : d53709 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53709, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53710 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53711 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53712 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53719 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5193 q ha hb
  have h13 (q : Pattern) (ha : d53720 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53720, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53721 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53722 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53723 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53724 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5195 (p : Pattern) (ha : d53730 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5194 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5196 (p : Pattern) (ha : d53735 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1175 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1176 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1177 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53735 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5197 (p : Pattern) (ha : d53746 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53742 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53742, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53743 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53744 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53745 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53746 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5198 (p : Pattern) (ha : d53752 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5100 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1180 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53733 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53734 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53736 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5196 q ha hb
  have h8 (q : Pattern) (ha : d53737 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53737, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53738 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53739 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53740 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53747 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5197 q ha hb
  have h13 (q : Pattern) (ha : d53748 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53748, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53749 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53750 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53751 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53752 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5199 (p : Pattern) (ha : d53758 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5198 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5200 (p : Pattern) (ha : d53764 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1636 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1637 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1638 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53764 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5201 (p : Pattern) (ha : d53775 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53771 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53771, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53772 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53773 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53774 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53775 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5202 (p : Pattern) (ha : d53781 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5108 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5109 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1641 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53762 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53763 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53765 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5200 q ha hb
  have h8 (q : Pattern) (ha : d53766 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53766, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53767 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53768 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53769 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53776 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5201 q ha hb
  have h13 (q : Pattern) (ha : d53777 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53777, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53778 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53779 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53780 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53781 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5203 (p : Pattern) (ha : d53787 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5202 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5204 (p : Pattern) (ha : d53794 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2119 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2120 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2121 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53794 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5205 (p : Pattern) (ha : d53805 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53801 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53801, d73190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53802 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53803 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53804 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53805 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5206 (p : Pattern) (ha : d53811 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5116 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5117 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2124 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53792 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53793 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53795 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5204 q ha hb
  have h8 (q : Pattern) (ha : d53796 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53796, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53797 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d53798 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d53799 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53806 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5205 q ha hb
  have h13 (q : Pattern) (ha : d53807 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53807, d73191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d53808 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53809 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53810 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d53811 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro5207 (p : Pattern) (ha : d53817 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5206 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5208 (p : Pattern) (ha : d53823 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5187 q ha hb
    | true =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5191 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5195 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5199 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5203 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5207 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5209 (p : Pattern) (ha : d53829 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5208 q ha hb
    | true =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5210 (p : Pattern) (ha : d53835 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5209 q ha hb
    | true =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5211 (p : Pattern) (ha : d53841 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5210 q ha hb
    | true =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5212 (p : Pattern) (ha : d53847 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5211 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5213 (p : Pattern) (ha : d53853 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5212 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5214 (p : Pattern) (ha : d53859 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5213 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5215 (p : Pattern) (ha : d53865 p = 1) (hb : d73191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5214 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d73191 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5216 (p : Pattern) (ha : d61679 p = 1) (hb : d61807 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (ha : d61679 q = 1) (hb : d61807 q = 1) : d61679 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5217 (p : Pattern) (ha : d3324 p = 1) (hb : d54187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51907 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3319 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6 q ha hb
    | true =>
      simp only [d3319, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3320 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3320, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3321 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3321, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3322 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3322, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51916 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3323 q = 1) (hb : d51917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3323, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3324 q = 1) (hb : d54187 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3324, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro5218 (p : Pattern) (ha : d54192 p = 1) (hb : d61544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d3329, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3331 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3331, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d61539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q hb ha
    | true =>
      simp only [d52030, d61539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d52033 q = 1) (hb : d61540 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52033, d61540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52034 q = 1) (hb : d61541 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52034, d61541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52035 q = 1) (hb : d61542 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d61542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52043 q = 1) (hb : d61543 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52043, d61543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54192 q = 1) (hb : d61544 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54192, d61544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro5219 (p : Pattern) (ha : d54198 p = 1) (hb : d61555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d3343, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3345 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3345, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d61550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q hb ha
    | true =>
      simp only [d52162, d61550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51963 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3347 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d3347, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52165 q = 1) (hb : d61551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52165, d61551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52166 q = 1) (hb : d61552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52166, d61552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52167 q = 1) (hb : d61553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d61553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52177 q = 1) (hb : d61554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52177, d61554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54198 q = 1) (hb : d61555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54198, d61555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5220 (p : Pattern) (ha : d54204 p = 1) (hb : d61561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3325 q = 1) (hb : d54188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3325, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5217 q ha hb
  have h2 (q : Pattern) (ha : d3326 q = 1) (hb : d54189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3326, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3327 q = 1) (hb : d54190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3327, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3328 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3328, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54193 q = 1) (hb : d61545 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54193, d61545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5218 q ha hb
  have h6 (q : Pattern) (ha : d54194 q = 1) (hb : d61546 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54194, d61546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54195 q = 1) (hb : d61547 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54195, d61547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54196 q = 1) (hb : d61548 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54196, d61548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54197 q = 1) (hb : d61549 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54197, d61549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54199 q = 1) (hb : d61556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54199, d61556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5219 q ha hb
  have h11 (q : Pattern) (ha : d54200 q = 1) (hb : d61557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54200, d61557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54201 q = 1) (hb : d61558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54201, d61558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54202 q = 1) (hb : d61559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54202, d61559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54203 q = 1) (hb : d61560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54203, d61560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54204 q = 1) (hb : d61561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54204, d61561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5221 (p : Pattern) (ha : d54205 p = 1) (hb : d61567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d3359, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3361 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3361, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d61562 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q hb ha
    | true =>
      simp only [d52336, d61562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3363 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d3363, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52350 q = 1) (hb : d61563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52350, d61563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52351 q = 1) (hb : d61564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52351, d61564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52352 q = 1) (hb : d61565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d61565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52362 q = 1) (hb : d61566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52362, d61566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54205 q = 1) (hb : d61567 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54205, d61567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5222 (p : Pattern) (ha : d54211 p = 1) (hb : d61573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d61568 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d61568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5221 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d61569 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d61569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d61570 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d61570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d61571 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d61571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d61572 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d61572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d61573 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d61573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5223 (p : Pattern) (ha : d54213 p = 1) (hb : d61580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52476 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d3376, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3378 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3378, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d61575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q hb ha
    | true =>
      simp only [d52557, d61575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3380 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d3380, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52571 q = 1) (hb : d61576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52571, d61576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52572 q = 1) (hb : d61577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52572, d61577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52573 q = 1) (hb : d61578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d61578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52583 q = 1) (hb : d61579 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52583, d61579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54213 q = 1) (hb : d61580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54213, d61580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5224 (p : Pattern) (ha : d54219 p = 1) (hb : d61586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d61581 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d61581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5223 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d61582 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d61582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d61583 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d61583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d61584 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d61584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d61585 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d61585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d61586 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d61586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5225 (p : Pattern) (ha : d54222 p = 1) (hb : d61594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d3394, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3396 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3396, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d61589 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q hb ha
    | true =>
      simp only [d52837, d61589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3398 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d3398, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52851 q = 1) (hb : d61590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52851, d61590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d52852 q = 1) (hb : d61591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52852, d61591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d52853 q = 1) (hb : d61592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d61592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d52863 q = 1) (hb : d61593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52863, d61593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54222 q = 1) (hb : d61594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54222, d61594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5226 (p : Pattern) (ha : d54228 p = 1) (hb : d61600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d61595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d61595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5225 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d61596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d61596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d61597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d61597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d61598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d61598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d61599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d61599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d61600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d61600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5227 (p : Pattern) (ha : d54232 p = 1) (hb : d61609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d3413, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3415 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3415, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d61604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q hb ha
    | true =>
      simp only [d53152, d61604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3417 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d3417, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53166 q = 1) (hb : d61605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53166, d61605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53167 q = 1) (hb : d61606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53167, d61606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53168 q = 1) (hb : d61607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d61607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d53178 q = 1) (hb : d61608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53178, d61608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54232 q = 1) (hb : d61609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54232, d61609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5228 (p : Pattern) (ha : d54238 p = 1) (hb : d61615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d61610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d61610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5227 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d61611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d61611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d61612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d61612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d61613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d61613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d61614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d61614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d61615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d61615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5229 (p : Pattern) (ha : d54243 p = 1) (hb : d61625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3433 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d3433, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3434 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3434, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3435 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3435, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d61620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q hb ha
    | true =>
      simp only [d53469, d61620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d3437 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d3437, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53483 q = 1) (hb : d61621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53483, d61621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d53484 q = 1) (hb : d61622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53484, d61622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d53485 q = 1) (hb : d61623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d61623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d53495 q = 1) (hb : d61624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53495, d61624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d54243 q = 1) (hb : d61625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d54243, d61625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h15 p ha hb
theorem andIntro5230 (p : Pattern) (ha : d54249 p = 1) (hb : d61631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d61626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d61626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5229 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d61627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d61627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d61628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d61628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d61629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d61629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d61630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d61630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d61631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d61631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5231 (p : Pattern) (ha : d54255 p = 1) (hb : d61637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d61574 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5220 q ha hb
    | true =>
      simp only [d54212, d61574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5222 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d61587 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d61587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5224 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d61588 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d61588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d61601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d61601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5226 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d61602 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d61602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d61603 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d61603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d61616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d61616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5228 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d61617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d61617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d61618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d61618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d61619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d61619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d61632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d61632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5230 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d61633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d61633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d61634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d61634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d61635 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d61635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d61636 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d61636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d61637 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d61637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5232 (p : Pattern) (ha : d54261 p = 1) (hb : d61643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d61638 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5231 q ha hb
    | true =>
      simp only [d54256, d61638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d61639 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d61639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d61640 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d61640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d61641 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d61641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d61642 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d61642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d61643 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d61643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5233 (p : Pattern) (ha : d54267 p = 1) (hb : d61649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d61644 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5232 q ha hb
    | true =>
      simp only [d54262, d61644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d61645 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d61645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d61646 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d61646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d61647 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d61647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d61648 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d61648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d61649 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d61649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5234 (p : Pattern) (ha : d54273 p = 1) (hb : d61655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d61650 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5233 q ha hb
    | true =>
      simp only [d54268, d61650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d61651 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d61651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d61652 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d61652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d61653 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d61653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d61654 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d61654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d61655 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d61655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5235 (p : Pattern) (ha : d54279 p = 1) (hb : d61661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d61656 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5234 q ha hb
    | true =>
      simp only [d54274, d61656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d61657 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d61657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d61658 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d61658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d61659 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d61659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d61660 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d61660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d61661 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d61661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5236 (p : Pattern) (ha : d54285 p = 1) (hb : d61667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d61662 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5235 q ha hb
    | true =>
      simp only [d54280, d61662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d61663 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d61663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d61664 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d61664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d61665 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d61665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d61666 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d61666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d61667 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d61667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5237 (p : Pattern) (ha : d54291 p = 1) (hb : d61673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d61668 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5236 q ha hb
    | true =>
      simp only [d54286, d61668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d61669 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d61669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d61670 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d61670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d61671 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d61671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d61672 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d61672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d61673 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d61673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5238 (p : Pattern) (ha : d54297 p = 1) (hb : d61679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d61674 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5237 q ha hb
    | true =>
      simp only [d54292, d61674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d61675 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d61675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d61676 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d61676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d61677 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d61677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d61678 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d61678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d61679 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d61679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5239 (p : Pattern) (ha : d61806 p = 1) (hb : d61807 p = 1) : d61806 p = 1 := by
  have h0 (q : Pattern) (ha : d61806 q = 1) (hb : d61807 q = 1) : d61806 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5240 (p : Pattern) (ha : d54192 p = 1) (hb : d61683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3329 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro323 q ha hb
    | true =>
      simp only [d3329, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3330 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3330, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52034 q = 1) (hb : d61680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52034, d61680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52035 q = 1) (hb : d61681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d61681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52043 q = 1) (hb : d61682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52043, d61682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54192 q = 1) (hb : d61683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54192, d61683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5241 (p : Pattern) (ha : d54198 p = 1) (hb : d61692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3343 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro328 q ha hb
    | true =>
      simp only [d3343, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3344 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3344, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52166 q = 1) (hb : d61689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52166, d61689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52167 q = 1) (hb : d61690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d61690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52177 q = 1) (hb : d61691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52177, d61691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54198 q = 1) (hb : d61692 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54198, d61692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5242 (p : Pattern) (ha : d54204 p = 1) (hb : d61698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54193 q = 1) (hb : d61684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54193, d61684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5240 q ha hb
  have h3 (q : Pattern) (ha : d54194 q = 1) (hb : d61685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54194, d61685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54195 q = 1) (hb : d61686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54195, d61686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54196 q = 1) (hb : d61687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54196, d61687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54197 q = 1) (hb : d61688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54197, d61688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54199 q = 1) (hb : d61693 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54199, d61693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5241 q ha hb
  have h8 (q : Pattern) (ha : d54200 q = 1) (hb : d61694 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54200, d61694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54201 q = 1) (hb : d61695 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54201, d61695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54202 q = 1) (hb : d61696 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54202, d61696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54203 q = 1) (hb : d61697 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54203, d61697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54204 q = 1) (hb : d61698 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54204, d61698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5243 (p : Pattern) (ha : d54205 p = 1) (hb : d61702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3359 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro334 q ha hb
    | true =>
      simp only [d3359, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3360 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3360, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52351 q = 1) (hb : d61699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52351, d61699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52352 q = 1) (hb : d61700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d61700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52362 q = 1) (hb : d61701 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52362, d61701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54205 q = 1) (hb : d61702 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54205, d61702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5244 (p : Pattern) (ha : d54211 p = 1) (hb : d61708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d61703 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d61703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5243 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d61704 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d61704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d61705 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d61705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d61706 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d61706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d61707 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d61707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d61708 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d61708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5245 (p : Pattern) (ha : d54213 p = 1) (hb : d61713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3376 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro340 q ha hb
    | true =>
      simp only [d3376, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3377 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3377, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52572 q = 1) (hb : d61710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52572, d61710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52573 q = 1) (hb : d61711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d61711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52583 q = 1) (hb : d61712 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52583, d61712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54213 q = 1) (hb : d61713 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54213, d61713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5246 (p : Pattern) (ha : d54219 p = 1) (hb : d61719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d61714 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d61714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5245 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d61715 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d61715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d61716 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d61716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d61717 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d61717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d61718 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d61718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d61719 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d61719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5247 (p : Pattern) (ha : d54222 p = 1) (hb : d61725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3394 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro346 q ha hb
    | true =>
      simp only [d3394, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3395 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3395, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52852 q = 1) (hb : d61722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52852, d61722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d52853 q = 1) (hb : d61723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d61723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52863 q = 1) (hb : d61724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52863, d61724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54222 q = 1) (hb : d61725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54222, d61725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro5248 (p : Pattern) (ha : d54228 p = 1) (hb : d61731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d61726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d61726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5247 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d61727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d61727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d61728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d61728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d61729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d61729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d61730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d61730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d61731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d61731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5249 (p : Pattern) (ha : d54232 p = 1) (hb : d61738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3413 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro352 q ha hb
    | true =>
      simp only [d3413, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3414 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3414, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53167 q = 1) (hb : d61735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53167, d61735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d53168 q = 1) (hb : d61736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d61736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53178 q = 1) (hb : d61737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53178, d61737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54232 q = 1) (hb : d61738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54232, d61738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
end NetHack.Soko22Hazard87
