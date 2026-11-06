import NetHack.Soko22Hazard87.AndIntroBlocks0312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro78250 (p : Pattern) (ha : d303886 p = 1) (hb : d305362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303860 q = 1) (hb : d305336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303860, d305336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78242 q ha hb
    | true =>
      simp only [d303860, d305336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303861 q = 1) (hb : d305337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303861, d305337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303861, d305337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303862 q = 1) (hb : d305338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d303862, d305338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303862, d305338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303863 q = 1) (hb : d305339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d303863, d305339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303863, d305339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303864 q = 1) (hb : d305340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d303864, d305340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303864, d305340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d303886 q = 1) (hb : d305362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303886, d305362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303886, d305362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78251 (p : Pattern) (ha : d303892 p = 1) (hb : d305368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303815 q = 1) (hb : d305301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303815, d305301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78234 q ha hb
    | true =>
      simp only [d303815, d305301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78235 q ha hb
  have h2 (q : Pattern) (ha : d303816 q = 1) (hb : d305302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303816, d305302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303816, d305302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303817 q = 1) (hb : d305303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303817, d305303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303817, d305303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303818 q = 1) (hb : d305304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303818, d305304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303818, d305304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303825 q = 1) (hb : d305311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303825, d305311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78236 q ha hb
    | true =>
      simp only [d303825, d305311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78237 q ha hb
  have h6 (q : Pattern) (ha : d303826 q = 1) (hb : d305312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303826, d305312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303826, d305312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303827 q = 1) (hb : d305313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303827, d305313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303827, d305313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d303841 q = 1) (hb : d305327 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303841, d305327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78240 q ha hb
    | true =>
      simp only [d303841, d305327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78228 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d303792 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d303842 q = 1) (hb : d305328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303842, d305328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303842, d305328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d303866 q = 1) (hb : d305342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303866, d305342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78243 q ha hb
    | true =>
      simp only [d303866, d305342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d303867 q = 1) (hb : d305343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303867, d305343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d303867, d305343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d303868 q = 1) (hb : d305344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303868, d305344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303868, d305344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d303869 q = 1) (hb : d305345 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303869, d305345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303869, d305345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d303870 q = 1) (hb : d305346 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303870, d305346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303870, d305346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d303874 q = 1) (hb : d305350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303874, d305350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78245 q ha hb
    | true =>
      simp only [d303874, d305350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78246 q ha hb
  have h17 (q : Pattern) (ha : d303875 q = 1) (hb : d305351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303875, d305351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303875, d305351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d303876 q = 1) (hb : d305352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303876, d305352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d303876, d305352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d303877 q = 1) (hb : d305353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303877, d305353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303877, d305353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d303880 q = 1) (hb : d305356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303880, d305356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78247 q ha hb
    | true =>
      simp only [d303880, d305356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78248 q ha hb
  have h21 (q : Pattern) (ha : d303881 q = 1) (hb : d305357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303881, d305357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303881, d305357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d303882 q = 1) (hb : d305358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303882, d305358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d303882, d305358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d303884 q = 1) (hb : d305360 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303884, d305360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78249 q ha hb
    | true =>
      simp only [d303884, d305360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78231 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d303802 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d303885 q = 1) (hb : d305361 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303885, d305361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d303885, d305361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d303887 q = 1) (hb : d305363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303887, d305363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78250 q ha hb
    | true =>
      simp only [d303887, d305363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d303888 q = 1) (hb : d305364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303888, d305364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d303888, d305364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d303889 q = 1) (hb : d305365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303889, d305365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d303889, d305365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d303890 q = 1) (hb : d305366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303890, d305366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d303890, d305366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d303891 q = 1) (hb : d305367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303891, d305367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d303891, d305367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d303892 q = 1) (hb : d305368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303892, d305368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d303892, d305368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro78252 (p : Pattern) (ha : d303899 p = 1) (hb : d305375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303792 q = 1) (hb : d305278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78228 q ha hb
    | true =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78229 q ha hb
  have h2 (q : Pattern) (ha : d303793 q = 1) (hb : d305279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303793, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303793, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303794 q = 1) (hb : d305280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303794, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303794, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303795 q = 1) (hb : d305281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303795, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303795, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303796 q = 1) (hb : d305282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303796, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303796, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303894 q = 1) (hb : d305370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303894, d305370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78229 q ha hb
    | true =>
      simp only [d303894, d305370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303895 q = 1) (hb : d305371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303895, d305371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303895, d305371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303896 q = 1) (hb : d305372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303896, d305372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303896, d305372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d303897 q = 1) (hb : d305373 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303897, d305373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303897, d305373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303898 q = 1) (hb : d305374 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303898, d305374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303898, d305374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303899 q = 1) (hb : d305375 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303899, d305375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303899, d305375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78253 (p : Pattern) (ha : d303905 p = 1) (hb : d305381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303894 q = 1) (hb : d305370 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303894, d305370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78229 q ha hb
    | true =>
      simp only [d303894, d305370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303895 q = 1) (hb : d305371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303895, d305371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303895, d305371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303896 q = 1) (hb : d305372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303896, d305372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303896, d305372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303897 q = 1) (hb : d305373 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303897, d305373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303897, d305373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303898 q = 1) (hb : d305374 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303898, d305374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303898, d305374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303900 q = 1) (hb : d305376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303900, d305376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78232 q ha hb
    | true =>
      simp only [d303900, d305376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303901 q = 1) (hb : d305377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303901, d305377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303901, d305377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303902 q = 1) (hb : d305378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303902, d305378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303902, d305378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d303903 q = 1) (hb : d305379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303903, d305379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303903, d305379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303904 q = 1) (hb : d305380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303904, d305380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303904, d305380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303905 q = 1) (hb : d305381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303905, d305381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303905, d305381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78254 (p : Pattern) (ha : d303912 p = 1) (hb : d305388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303884 q = 1) (hb : d305360 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303884, d305360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78249 q ha hb
    | true =>
      simp only [d303884, d305360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78231 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303885 q = 1) (hb : d305361 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303885, d305361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303885, d305361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d303887 q = 1) (hb : d305363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303887, d305363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78250 q ha hb
    | true =>
      simp only [d303887, d305363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303888 q = 1) (hb : d305364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303888, d305364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303888, d305364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d303889 q = 1) (hb : d305365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303889, d305365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303889, d305365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303910 q = 1) (hb : d305386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303910, d305386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303910, d305386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303911 q = 1) (hb : d305387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303911, d305387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303911, d305387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303912 q = 1) (hb : d305388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303912, d305388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303912, d305388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro78255 (p : Pattern) (ha : d303914 p = 1) (hb : d305390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303900 q = 1) (hb : d305376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303900, d305376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78232 q ha hb
    | true =>
      simp only [d303900, d305376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303901 q = 1) (hb : d305377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303901, d305377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303901, d305377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303902 q = 1) (hb : d305378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303902, d305378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303902, d305378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303903 q = 1) (hb : d305379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303903, d305379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303903, d305379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303904 q = 1) (hb : d305380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303904, d305380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303904, d305380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303914 q = 1) (hb : d305390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303914, d305390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303914, d305390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78256 (p : Pattern) (ha : d303925 p = 1) (hb : d305401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303920 q = 1) (hb : d305396 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
  have h2 (q : Pattern) (ha : d303738 q = 1) (hb : d305239 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
    | true =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303921 q = 1) (hb : d305397 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303739 q = 1) (hb : d305240 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303922 q = 1) (hb : d305398 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303923 q = 1) (hb : d305399 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303924 q = 1) (hb : d305400 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303924, d305400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303924, d305400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303925 q = 1) (hb : d305401 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d303925, d305401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303925, d305401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78257 (p : Pattern) (ha : d303931 p = 1) (hb : d305407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303920 q = 1) (hb : d305396 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
  have h2 (q : Pattern) (ha : d303738 q = 1) (hb : d305239 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
    | true =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303921 q = 1) (hb : d305397 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303739 q = 1) (hb : d305240 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303922 q = 1) (hb : d305398 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303923 q = 1) (hb : d305399 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303924 q = 1) (hb : d305400 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303924, d305400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303924, d305400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303926 q = 1) (hb : d305402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
  have h9 (q : Pattern) (ha : d303753 q = 1) (hb : d305245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
    | true =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d303927 q = 1) (hb : d305403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303754 q = 1) (hb : d305246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d303928 q = 1) (hb : d305404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d303929 q = 1) (hb : d305405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d303930 q = 1) (hb : d305406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d303931 q = 1) (hb : d305407 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d303931, d305407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303931, d305407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78258 (p : Pattern) (ha : d303936 p = 1) (hb : d305412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303920 q = 1) (hb : d305396 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
  have h2 (q : Pattern) (ha : d303738 q = 1) (hb : d305239 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
    | true =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303921 q = 1) (hb : d305397 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303739 q = 1) (hb : d305240 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303922 q = 1) (hb : d305398 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303923 q = 1) (hb : d305399 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303926 q = 1) (hb : d305402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
  have h8 (q : Pattern) (ha : d303753 q = 1) (hb : d305245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
    | true =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d303927 q = 1) (hb : d305403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303754 q = 1) (hb : d305246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d303928 q = 1) (hb : d305404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d303929 q = 1) (hb : d305405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d303930 q = 1) (hb : d305406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d303935 q = 1) (hb : d305411 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303935, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303935, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d303936 q = 1) (hb : d305412 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d303936, d305412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303936, d305412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78259 (p : Pattern) (ha : d303946 p = 1) (hb : d305417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303926 q = 1) (hb : d305402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
  have h2 (q : Pattern) (ha : d303753 q = 1) (hb : d305245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
    | true =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303927 q = 1) (hb : d305403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303754 q = 1) (hb : d305246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303928 q = 1) (hb : d305404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303929 q = 1) (hb : d305405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303935 q = 1) (hb : d305411 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303935, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303935, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303945 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303946 q = 1) (hb : d305417 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d303946, d305417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303946, d305417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro78260 (p : Pattern) (ha : d303952 p = 1) (hb : d305423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303932 q = 1) (hb : d305408 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303932, d305408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78256 q ha hb
    | true =>
      simp only [d303932, d305408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78257 q ha hb
  have h2 (q : Pattern) (ha : d303933 q = 1) (hb : d305409 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303933, d305409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303933, d305409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303934 q = 1) (hb : d305410 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303934, d305410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303934, d305410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303937 q = 1) (hb : d305413 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78257 q ha hb
    | true =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
  have h5 (q : Pattern) (ha : d303938 q = 1) (hb : d305414 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303939 q = 1) (hb : d305415 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303940 q = 1) (hb : d305416 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303940, d305416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303940, d305416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303947 q = 1) (hb : d305418 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
    | true =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78259 q ha hb
  have h9 (q : Pattern) (ha : d303948 q = 1) (hb : d305419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303949 q = 1) (hb : d305420 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303950 q = 1) (hb : d305421 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d303951 q = 1) (hb : d305422 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d303951, d305422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303951, d305422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d303952 q = 1) (hb : d305423 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d303952, d305423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303952, d305423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro78261 (p : Pattern) (ha : d303957 p = 1) (hb : d305428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303937 q = 1) (hb : d305413 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78257 q ha hb
    | true =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
  have h2 (q : Pattern) (ha : d303938 q = 1) (hb : d305414 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303939 q = 1) (hb : d305415 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303947 q = 1) (hb : d305418 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
    | true =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78259 q ha hb
  have h5 (q : Pattern) (ha : d303948 q = 1) (hb : d305419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303949 q = 1) (hb : d305420 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303950 q = 1) (hb : d305421 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303955 q = 1) (hb : d305426 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303955, d305426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303955, d305426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d303956 q = 1) (hb : d305427 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d303956, d305427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303956, d305427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303957 q = 1) (hb : d305428 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d303957, d305428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303957, d305428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro78262 (p : Pattern) (ha : d303963 p = 1) (hb : d305434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303953 q = 1) (hb : d305424 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303953, d305424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78260 q ha hb
    | true =>
      simp only [d303953, d305424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303954 q = 1) (hb : d305425 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303954, d305425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303954, d305425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303958 q = 1) (hb : d305429 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303958, d305429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78261 q ha hb
    | true =>
      simp only [d303958, d305429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303959 q = 1) (hb : d305430 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303959, d305430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303959, d305430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303960 q = 1) (hb : d305431 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d303960, d305431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303960, d305431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303961 q = 1) (hb : d305432 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d303961, d305432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303961, d305432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303962 q = 1) (hb : d305433 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d303962, d305433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303962, d305433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d303963 q = 1) (hb : d305434 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303963, d305434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303963, d305434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro78263 (p : Pattern) (ha : d303965 p = 1) (hb : d305436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303947 q = 1) (hb : d305418 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
    | true =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78259 q ha hb
  have h2 (q : Pattern) (ha : d303948 q = 1) (hb : d305419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303949 q = 1) (hb : d305420 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303955 q = 1) (hb : d305426 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303955, d305426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303955, d305426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303964 q = 1) (hb : d305435 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d303964, d305435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303964, d305435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d303965 q = 1) (hb : d305436 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d303965, d305436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303965, d305436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78264 (p : Pattern) (ha : d303971 p = 1) (hb : d305442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303958 q = 1) (hb : d305429 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303958, d305429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78261 q ha hb
    | true =>
      simp only [d303958, d305429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303959 q = 1) (hb : d305430 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303959, d305430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303959, d305430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303966 q = 1) (hb : d305437 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303966, d305437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78263 q ha hb
    | true =>
      simp only [d303966, d305437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303967 q = 1) (hb : d305438 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303967, d305438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303967, d305438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303968 q = 1) (hb : d305439 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d303968, d305439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303968, d305439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303969 q = 1) (hb : d305440 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d303969, d305440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303969, d305440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303970 q = 1) (hb : d305441 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d303970, d305441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303970, d305441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d303971 q = 1) (hb : d305442 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303971, d305442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303971, d305442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro78265 (p : Pattern) (ha : d303984 p = 1) (hb : d305445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303920 q = 1) (hb : d305396 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303920, d305396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
  have h2 (q : Pattern) (ha : d303738 q = 1) (hb : d305239 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78221 q ha hb
    | true =>
      simp only [d303738, d305239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303921 q = 1) (hb : d305397 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303921, d305397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303739 q = 1) (hb : d305240 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303739, d305240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303922 q = 1) (hb : d305398 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303922, d305398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303923 q = 1) (hb : d305399 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303923, d305399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d303926 q = 1) (hb : d305402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303926, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
  have h8 (q : Pattern) (ha : d303753 q = 1) (hb : d305245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78222 q ha hb
    | true =>
      simp only [d303753, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d303927 q = 1) (hb : d305403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303927, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303754 q = 1) (hb : d305246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303754, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d303928 q = 1) (hb : d305404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303928, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d303929 q = 1) (hb : d305405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d303929, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d303930 q = 1) (hb : d305406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303930, d305406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303983 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303984 q = 1) (hb : d305445 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d303984, d305445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303984, d305445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro78266 (p : Pattern) (ha : d303991 p = 1) (hb : d305451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303937 q = 1) (hb : d305413 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78257 q ha hb
    | true =>
      simp only [d303937, d305413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
  have h2 (q : Pattern) (ha : d303938 q = 1) (hb : d305414 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303938, d305414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303939 q = 1) (hb : d305415 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303939, d305415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303947 q = 1) (hb : d305418 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78258 q ha hb
    | true =>
      simp only [d303947, d305418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78259 q ha hb
  have h5 (q : Pattern) (ha : d303948 q = 1) (hb : d305419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303948, d305419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303949 q = 1) (hb : d305420 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303949, d305420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303950 q = 1) (hb : d305421 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303950, d305421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303985 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303986 q = 1) (hb : d305446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d303986, d305446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78265 q ha hb
    | true =>
      simp only [d303986, d305446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d303987 q = 1) (hb : d305447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d303987, d305447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303987, d305447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303988 q = 1) (hb : d305448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d303988, d305448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303988, d305448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d303989 q = 1) (hb : d305449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d303989, d305449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d303989, d305449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d303990 q = 1) (hb : d305450 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d303990, d305450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303990, d305450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d303991 q = 1) (hb : d305451 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d303991, d305451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303991, d305451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro78267 (p : Pattern) (ha : d303997 p = 1) (hb : d305457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303992 q = 1) (hb : d305452 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303992, d305452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78266 q ha hb
    | true =>
      simp only [d303992, d305452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303993 q = 1) (hb : d305453 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303993, d305453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303993, d305453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303994 q = 1) (hb : d305454 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d303994, d305454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303994, d305454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303995 q = 1) (hb : d305455 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d303995, d305455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303995, d305455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303996 q = 1) (hb : d305456 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d303996, d305456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303996, d305456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d303997 q = 1) (hb : d305457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303997, d305457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303997, d305457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78268 (p : Pattern) (ha : d304003 p = 1) (hb : d305463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303972 q = 1) (hb : d305443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303972, d305443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78262 q ha hb
    | true =>
      simp only [d303972, d305443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78264 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303978 q = 1) (hb : d305444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303978, d305444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303978, d305444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d303998 q = 1) (hb : d305458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303998, d305458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78267 q ha hb
    | true =>
      simp only [d303998, d305458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303999 q = 1) (hb : d305459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303999, d305459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303999, d305459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304000 q = 1) (hb : d305460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304000, d305460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304000, d305460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304001 q = 1) (hb : d305461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304001, d305461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304001, d305461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304002 q = 1) (hb : d305462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304002, d305462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304002, d305462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304003 q = 1) (hb : d305463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304003, d305463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304003, d305463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro78269 (p : Pattern) (ha : d303976 p = 1) (hb : d305468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303966 q = 1) (hb : d305437 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d303966, d305437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78263 q ha hb
    | true =>
      simp only [d303966, d305437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d303967 q = 1) (hb : d305438 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d303967, d305438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303967, d305438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303973 q = 1) (hb : d305465 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d303973, d305465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303973, d305465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d303974 q = 1) (hb : d305466 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d303974, d305466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303974, d305466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303975 q = 1) (hb : d305467 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d303975, d305467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303975, d305467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d303976 q = 1) (hb : d305468 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303976, d305468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303976, d305468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78270 (p : Pattern) (ha : d304010 p = 1) (hb : d305474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304005 q = 1) (hb : d305469 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304005, d305469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78269 q ha hb
    | true =>
      simp only [d304005, d305469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304006 q = 1) (hb : d305470 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304006, d305470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304006, d305470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d304007 q = 1) (hb : d305471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304007, d305471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304007, d305471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304008 q = 1) (hb : d305472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304008, d305472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304008, d305472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304009 q = 1) (hb : d305473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304009, d305473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304009, d305473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304010 q = 1) (hb : d305474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304010, d305474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304010, d305474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78271 (p : Pattern) (ha : d304016 p = 1) (hb : d305480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303798 q = 1) (hb : d305284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303798, d305284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303798, d305284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78230 q ha hb
  have h2 (q : Pattern) (ha : d303799 q = 1) (hb : d305285 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303799, d305285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303799, d305285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d303808 q = 1) (hb : d305294 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303808, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78230 q ha hb
    | true =>
      simp only [d303808, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78233 q ha hb
  have h4 (q : Pattern) (ha : d303809 q = 1) (hb : d305295 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303809, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303809, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d303810 q = 1) (hb : d305296 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303810, d305296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d303810, d305296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303893 q = 1) (hb : d305369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303893, d305369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78244 q ha hb
    | true =>
      simp only [d303893, d305369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78251 q ha hb
  have h7 (q : Pattern) (ha : d303906 q = 1) (hb : d305382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303906, d305382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78252 q ha hb
    | true =>
      simp only [d303906, d305382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78253 q ha hb
  have h8 (q : Pattern) (ha : d303907 q = 1) (hb : d305383 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303907, d305383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303907, d305383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303908 q = 1) (hb : d305384 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303908, d305384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303908, d305384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d303909 q = 1) (hb : d305385 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303909, d305385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303909, d305385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d303913 q = 1) (hb : d305389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303913, d305389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303913, d305389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78254 q ha hb
  have h12 (q : Pattern) (ha : d303915 q = 1) (hb : d305391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303915, d305391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303915, d305391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78255 q ha hb
  have h13 (q : Pattern) (ha : d303916 q = 1) (hb : d305392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303916, d305392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d303916, d305392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d303917 q = 1) (hb : d305393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303917, d305393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303917, d305393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d303918 q = 1) (hb : d305394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303918, d305394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d303918, d305394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d303919 q = 1) (hb : d305395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303919, d305395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303919, d305395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304004 q = 1) (hb : d305464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304004, d305464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304004, d305464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78268 q ha hb
  have h18 (q : Pattern) (ha : d304011 q = 1) (hb : d305475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304011, d305475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304011, d305475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78270 q ha hb
  have h19 (q : Pattern) (ha : d304012 q = 1) (hb : d305476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304012, d305476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d304012, d305476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d304013 q = 1) (hb : d305477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d304013, d305477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d304013, d305477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d304014 q = 1) (hb : d305478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d304014, d305478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d304014, d305478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d304015 q = 1) (hb : d305479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d304015, d305479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d304015, d305479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d304016 q = 1) (hb : d305480 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d304016, d305480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d304016, d305480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro78272 (p : Pattern) (ha : d304022 p = 1) (hb : d305486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304017 q = 1) (hb : d305481 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d304017, d305481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304017, d305481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78271 q ha hb
  have h2 (q : Pattern) (ha : d304018 q = 1) (hb : d305482 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d304018, d305482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304018, d305482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d304019 q = 1) (hb : d305483 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d304019, d305483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304019, d305483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d304020 q = 1) (hb : d305484 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d304020, d305484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304020, d305484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304021 q = 1) (hb : d305485 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d304021, d305485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304021, d305485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304022 q = 1) (hb : d305486 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d304022, d305486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304022, d305486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78273 (p : Pattern) (ha : d304028 p = 1) (hb : d305492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d302880 q = 1) (hb : d304440 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d302880, d304440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78031 q ha hb
    | true =>
      simp only [d302880, d304440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78060 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303123 q = 1) (hb : d304680 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303123, d304680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303123, d304680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78107 q ha hb
  have h3 (q : Pattern) (ha : d303124 q = 1) (hb : d304681 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303124, d304681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303124, d304681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303392 q = 1) (hb : d304948 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303392, d304948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303392, d304948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78159 q ha hb
  have h5 (q : Pattern) (ha : d303393 q = 1) (hb : d304949 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303393, d304949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303393, d304949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303394 q = 1) (hb : d304950 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d303394, d304950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303394, d304950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303724 q = 1) (hb : d305228 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303724, d305228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303724, d305228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78219 q ha hb
  have h8 (q : Pattern) (ha : d303725 q = 1) (hb : d305229 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303725, d305229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303725, d305229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303726 q = 1) (hb : d305230 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d303726, d305230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303726, d305230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303727 q = 1) (hb : d305231 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d303727, d305231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303727, d305231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d304023 q = 1) (hb : d305487 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d304023, d305487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304023, d305487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78272 q ha hb
  have h12 (q : Pattern) (ha : d304024 q = 1) (hb : d305488 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d304024, d305488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304024, d305488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d304025 q = 1) (hb : d305489 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d304025, d305489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304025, d305489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d304026 q = 1) (hb : d305490 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d304026, d305490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304026, d305490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d304027 q = 1) (hb : d305491 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d304027, d305491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304027, d305491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304028 q = 1) (hb : d305492 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d304028, d305492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d304028, d305492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro78274 (p : Pattern) (ha : d304034 p = 1) (hb : d305498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304029 q = 1) (hb : d305493 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d304029, d305493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78273 q ha hb
    | true =>
      simp only [d304029, d305493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304030 q = 1) (hb : d305494 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d304030, d305494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304030, d305494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304031 q = 1) (hb : d305495 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d304031, d305495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304031, d305495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304032 q = 1) (hb : d305496 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d304032, d305496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304032, d305496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304033 q = 1) (hb : d305497 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d304033, d305497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304033, d305497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304034 q = 1) (hb : d305498 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d304034, d305498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304034, d305498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78275 (p : Pattern) (ha : d304040 p = 1) (hb : d305504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304035 q = 1) (hb : d305499 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d304035, d305499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78274 q ha hb
    | true =>
      simp only [d304035, d305499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304036 q = 1) (hb : d305500 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d304036, d305500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304036, d305500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304037 q = 1) (hb : d305501 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d304037, d305501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304037, d305501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304038 q = 1) (hb : d305502 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d304038, d305502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304038, d305502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304039 q = 1) (hb : d305503 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d304039, d305503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304039, d305503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304040 q = 1) (hb : d305504 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d304040, d305504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304040, d305504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78276 (p : Pattern) (ha : d304046 p = 1) (hb : d305510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304041 q = 1) (hb : d305505 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d304041, d305505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78275 q ha hb
    | true =>
      simp only [d304041, d305505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304042 q = 1) (hb : d305506 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d304042, d305506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304042, d305506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304043 q = 1) (hb : d305507 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d304043, d305507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304043, d305507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304044 q = 1) (hb : d305508 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d304044, d305508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304044, d305508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304045 q = 1) (hb : d305509 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d304045, d305509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304045, d305509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304046 q = 1) (hb : d305510 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d304046, d305510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304046, d305510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78277 (p : Pattern) (ha : d304052 p = 1) (hb : d305516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304047 q = 1) (hb : d305511 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d304047, d305511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78276 q ha hb
    | true =>
      simp only [d304047, d305511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304048 q = 1) (hb : d305512 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d304048, d305512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304048, d305512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304049 q = 1) (hb : d305513 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d304049, d305513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304049, d305513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304050 q = 1) (hb : d305514 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d304050, d305514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304050, d305514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304051 q = 1) (hb : d305515 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d304051, d305515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304051, d305515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304052 q = 1) (hb : d305516 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d304052, d305516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304052, d305516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78278 (p : Pattern) (ha : d304058 p = 1) (hb : d305522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304053 q = 1) (hb : d305517 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d304053, d305517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78277 q ha hb
    | true =>
      simp only [d304053, d305517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304054 q = 1) (hb : d305518 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d304054, d305518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304054, d305518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304055 q = 1) (hb : d305519 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d304055, d305519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304055, d305519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304056 q = 1) (hb : d305520 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d304056, d305520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304056, d305520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304057 q = 1) (hb : d305521 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d304057, d305521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304057, d305521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304058 q = 1) (hb : d305522 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d304058, d305522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304058, d305522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78279 (p : Pattern) (ha : d304064 p = 1) (hb : d305528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304059 q = 1) (hb : d305523 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d304059, d305523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78278 q ha hb
    | true =>
      simp only [d304059, d305523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304060 q = 1) (hb : d305524 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d304060, d305524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304060, d305524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304061 q = 1) (hb : d305525 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d304061, d305525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304061, d305525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304062 q = 1) (hb : d305526 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d304062, d305526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304062, d305526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304063 q = 1) (hb : d305527 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d304063, d305527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304063, d305527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304064 q = 1) (hb : d305528 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d304064, d305528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304064, d305528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78280 (p : Pattern) (ha : d304070 p = 1) (hb : d305534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304065 q = 1) (hb : d305529 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d304065, d305529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78279 q ha hb
    | true =>
      simp only [d304065, d305529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304066 q = 1) (hb : d305530 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d304066, d305530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304066, d305530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304067 q = 1) (hb : d305531 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d304067, d305531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304067, d305531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304068 q = 1) (hb : d305532 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d304068, d305532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304068, d305532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304069 q = 1) (hb : d305533 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d304069, d305533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304069, d305533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304070 q = 1) (hb : d305534 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d304070, d305534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304070, d305534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78281 (p : Pattern) (ha : d53647 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77634 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77635 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77655 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77656 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78282 (p : Pattern) (ha : d282071 p = 1) (hb : d300100 p = 1) : d304381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30664 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
    | true =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
  have h2 (q : Pattern) (ha : d30724 q = 1) (hb : d300100 q = 1) : d304162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30725 q = 1) (hb : d300100 q = 1) : d304163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30725, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30726 q = 1) (hb : d300100 q = 1) : d304164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30727 q = 1) (hb : d300100 q = 1) : d304165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282071 q = 1) (hb : d300100 q = 1) : d304381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282071, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282071, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78283 (p : Pattern) (ha : d282081 p = 1) (hb : d300100 p = 1) : d304427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30700 q = 1) (hb : d300100 q = 1) : d304138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77652 q ha hb
    | true =>
      simp only [d30700, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77631 q ha hb
  have h2 (q : Pattern) (ha : d282077 q = 1) (hb : d300100 q = 1) : d304423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282077, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282077, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282078 q = 1) (hb : d300100 q = 1) : d304424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282078, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282078, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282079 q = 1) (hb : d300100 q = 1) : d304425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282079, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282079, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282080 q = 1) (hb : d300100 q = 1) : d304426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282080, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282080, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282081 q = 1) (hb : d300100 q = 1) : d304427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282081, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282081, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78284 (p : Pattern) (ha : d282087 p = 1) (hb : d300100 p = 1) : d305545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30729 q = 1) (hb : d300100 q = 1) : d304167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77657 q ha hb
    | true =>
      simp only [d30729, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77658 q ha hb
  have h2 (q : Pattern) (ha : d30730 q = 1) (hb : d300100 q = 1) : d304168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30730, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282069 q = 1) (hb : d300100 q = 1) : d305535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282069, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282069, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282070 q = 1) (hb : d300100 q = 1) : d305536 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282070, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282070, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282072 q = 1) (hb : d300100 q = 1) : d304382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282072, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282072, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78282 q ha hb
  have h6 (q : Pattern) (ha : d282073 q = 1) (hb : d300100 q = 1) : d305537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282073, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282073, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d282074 q = 1) (hb : d300100 q = 1) : d305538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282074, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282074, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d282075 q = 1) (hb : d300100 q = 1) : d305539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282075, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282075, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d282076 q = 1) (hb : d300100 q = 1) : d305540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282076, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282076, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282082 q = 1) (hb : d300100 q = 1) : d304428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282082, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282082, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78283 q ha hb
  have h11 (q : Pattern) (ha : d282083 q = 1) (hb : d300100 q = 1) : d305541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282083, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282083, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d282084 q = 1) (hb : d300100 q = 1) : d305542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282084, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282084, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d282085 q = 1) (hb : d300100 q = 1) : d305543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282085, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282085, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d282086 q = 1) (hb : d300100 q = 1) : d305544 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282086, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282086, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d282087 q = 1) (hb : d300100 q = 1) : d305545 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282087, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282087, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78285 (p : Pattern) (ha : d282093 p = 1) (hb : d300100 p = 1) : d305551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78281 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282088 q = 1) (hb : d300100 q = 1) : d305546 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282088, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282088, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78284 q ha hb
  have h7 (q : Pattern) (ha : d282089 q = 1) (hb : d300100 q = 1) : d305547 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282089, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282089, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d282090 q = 1) (hb : d300100 q = 1) : d305548 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282090, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282090, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d282091 q = 1) (hb : d300100 q = 1) : d305549 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282091, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282091, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282092 q = 1) (hb : d300100 q = 1) : d305550 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282092, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282092, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d282093 q = 1) (hb : d300100 q = 1) : d305551 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282093, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282093, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78286 (p : Pattern) (ha : d282096 p = 1) (hb : d300100 p = 1) : d305554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30940 q = 1) (hb : d300100 q = 1) : d304224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77688 q ha hb
    | true =>
      simp only [d30940, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77689 q ha hb
  have h2 (q : Pattern) (ha : d30941 q = 1) (hb : d300100 q = 1) : d304287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30942 q = 1) (hb : d300100 q = 1) : d304288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30942, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30943 q = 1) (hb : d300100 q = 1) : d304289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30944 q = 1) (hb : d300100 q = 1) : d304290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282096 q = 1) (hb : d300100 q = 1) : d305554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282096, d305554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282096, d305554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78287 (p : Pattern) (ha : d282107 p = 1) (hb : d300100 p = 1) : d305564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282102 q = 1) (hb : d300100 q = 1) : d304262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282102, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77725 q ha hb
    | true =>
      simp only [d282102, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77695 q ha hb
  have h2 (q : Pattern) (ha : d282103 q = 1) (hb : d300100 q = 1) : d305560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282103, d305560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282103, d305560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282104 q = 1) (hb : d300100 q = 1) : d305561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282104, d305561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282104, d305561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282105 q = 1) (hb : d300100 q = 1) : d305562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282105, d305562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282105, d305562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282106 q = 1) (hb : d300100 q = 1) : d305563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282106, d305563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282106, d305563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282107 q = 1) (hb : d300100 q = 1) : d305564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282107, d305564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282107, d305564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78288 (p : Pattern) (ha : d282113 p = 1) (hb : d300100 p = 1) : d305570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30946 q = 1) (hb : d300100 q = 1) : d304292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77687 q ha hb
    | true =>
      simp only [d30946, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77690 q ha hb
  have h2 (q : Pattern) (ha : d30947 q = 1) (hb : d300100 q = 1) : d304293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30947, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282094 q = 1) (hb : d300100 q = 1) : d305552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282094, d305552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282094, d305552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282095 q = 1) (hb : d300100 q = 1) : d305553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282095, d305553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282095, d305553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282097 q = 1) (hb : d300100 q = 1) : d305555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282097, d305555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282097, d305555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78286 q ha hb
  have h6 (q : Pattern) (ha : d282098 q = 1) (hb : d300100 q = 1) : d305556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282098, d305556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282098, d305556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d282099 q = 1) (hb : d300100 q = 1) : d305557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282099, d305557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282099, d305557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d282100 q = 1) (hb : d300100 q = 1) : d305558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282100, d305558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282100, d305558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d282101 q = 1) (hb : d300100 q = 1) : d305559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282101, d305559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282101, d305559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282108 q = 1) (hb : d300100 q = 1) : d305565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282108, d305565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282108, d305565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78287 q ha hb
  have h11 (q : Pattern) (ha : d282109 q = 1) (hb : d300100 q = 1) : d305566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282109, d305566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282109, d305566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d282110 q = 1) (hb : d300100 q = 1) : d305567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282110, d305567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282110, d305567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d282111 q = 1) (hb : d300100 q = 1) : d305568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282111, d305568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282111, d305568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d282112 q = 1) (hb : d300100 q = 1) : d305569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282112, d305569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282112, d305569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d282113 q = 1) (hb : d300100 q = 1) : d305570 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282113, d305570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282113, d305570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78289 (p : Pattern) (ha : d282119 p = 1) (hb : d300100 p = 1) : d305576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282114 q = 1) (hb : d300100 q = 1) : d305571 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282114, d305571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282114, d305571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78288 q ha hb
  have h2 (q : Pattern) (ha : d282115 q = 1) (hb : d300100 q = 1) : d305572 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282115, d305572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282115, d305572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282116 q = 1) (hb : d300100 q = 1) : d305573 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282116, d305573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282116, d305573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282117 q = 1) (hb : d300100 q = 1) : d305574 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282117, d305574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282117, d305574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282118 q = 1) (hb : d300100 q = 1) : d305575 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282118, d305575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282118, d305575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282119 q = 1) (hb : d300100 q = 1) : d305576 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282119, d305576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282119, d305576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78290 (p : Pattern) (ha : d282123 p = 1) (hb : d300100 p = 1) : d305580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31276 q = 1) (hb : d300100 q = 1) : d304468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77739 q ha hb
    | true =>
      simp only [d31276, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77740 q ha hb
  have h2 (q : Pattern) (ha : d31277 q = 1) (hb : d300100 q = 1) : d304469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31278 q = 1) (hb : d300100 q = 1) : d304470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31278, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31279 q = 1) (hb : d300100 q = 1) : d304471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31280 q = 1) (hb : d300100 q = 1) : d304472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282123 q = 1) (hb : d300100 q = 1) : d305580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282123, d305580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282123, d305580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78291 (p : Pattern) (ha : d282134 p = 1) (hb : d300100 p = 1) : d305591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282129 q = 1) (hb : d300100 q = 1) : d305586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282129, d305586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77780 q ha hb
    | true =>
      simp only [d282129, d305586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77748 q ha hb
  have h2 (q : Pattern) (ha : d282130 q = 1) (hb : d300100 q = 1) : d305587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282130, d305587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282130, d305587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282131 q = 1) (hb : d300100 q = 1) : d305588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282131, d305588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282131, d305588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282132 q = 1) (hb : d300100 q = 1) : d305589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282132, d305589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282132, d305589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282133 q = 1) (hb : d300100 q = 1) : d305590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282133, d305590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282133, d305590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282134 q = 1) (hb : d300100 q = 1) : d305591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282134, d305591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282134, d305591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78292 (p : Pattern) (ha : d282140 p = 1) (hb : d300100 p = 1) : d305597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31282 q = 1) (hb : d300100 q = 1) : d304474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d304474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77738 q ha hb
    | true =>
      simp only [d31282, d304474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77741 q ha hb
  have h2 (q : Pattern) (ha : d31283 q = 1) (hb : d300100 q = 1) : d304475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d304475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31283, d304475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282121 q = 1) (hb : d300100 q = 1) : d305578 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282121, d305578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282121, d305578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282122 q = 1) (hb : d300100 q = 1) : d305579 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282122, d305579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282122, d305579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282124 q = 1) (hb : d300100 q = 1) : d305581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282124, d305581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282124, d305581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78290 q ha hb
  have h6 (q : Pattern) (ha : d282125 q = 1) (hb : d300100 q = 1) : d305582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282125, d305582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282125, d305582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d282126 q = 1) (hb : d300100 q = 1) : d305583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282126, d305583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282126, d305583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d282127 q = 1) (hb : d300100 q = 1) : d305584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282127, d305584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282127, d305584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d282128 q = 1) (hb : d300100 q = 1) : d305585 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282128, d305585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282128, d305585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282135 q = 1) (hb : d300100 q = 1) : d305592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282135, d305592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282135, d305592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78291 q ha hb
  have h11 (q : Pattern) (ha : d282136 q = 1) (hb : d300100 q = 1) : d305593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282136, d305593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282136, d305593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d282137 q = 1) (hb : d300100 q = 1) : d305594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282137, d305594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282137, d305594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d282138 q = 1) (hb : d300100 q = 1) : d305595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282138, d305595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282138, d305595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d282139 q = 1) (hb : d300100 q = 1) : d305596 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282139, d305596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282139, d305596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d282140 q = 1) (hb : d300100 q = 1) : d305597 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282140, d305597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282140, d305597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78293 (p : Pattern) (ha : d282146 p = 1) (hb : d300100 p = 1) : d305603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282141 q = 1) (hb : d300100 q = 1) : d305598 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282141, d305598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282141, d305598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78292 q ha hb
  have h2 (q : Pattern) (ha : d282142 q = 1) (hb : d300100 q = 1) : d305599 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282142, d305599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282142, d305599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282143 q = 1) (hb : d300100 q = 1) : d305600 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282143, d305600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282143, d305600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282144 q = 1) (hb : d300100 q = 1) : d305601 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282144, d305601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282144, d305601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282145 q = 1) (hb : d300100 q = 1) : d305602 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282145, d305602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282145, d305602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282146 q = 1) (hb : d300100 q = 1) : d305603 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282146, d305603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282146, d305603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78294 (p : Pattern) (ha : d290378 p = 1) (hb : d300100 p = 1) : d305608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31710 q = 1) (hb : d300100 q = 1) : d304727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77801 q ha hb
    | true =>
      simp only [d31710, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77802 q ha hb
  have h2 (q : Pattern) (ha : d31711 q = 1) (hb : d300100 q = 1) : d304728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31712 q = 1) (hb : d300100 q = 1) : d304729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31712, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31713 q = 1) (hb : d300100 q = 1) : d304730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31714 q = 1) (hb : d300100 q = 1) : d304731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290378 q = 1) (hb : d300100 q = 1) : d305608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290378, d305608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290378, d305608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78295 (p : Pattern) (ha : d290389 p = 1) (hb : d300100 p = 1) : d305619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290384 q = 1) (hb : d300100 q = 1) : d305614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290384, d305614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77842 q ha hb
    | true =>
      simp only [d290384, d305614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77810 q ha hb
  have h2 (q : Pattern) (ha : d290385 q = 1) (hb : d300100 q = 1) : d305615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290385, d305615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290385, d305615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290386 q = 1) (hb : d300100 q = 1) : d305616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290386, d305616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290386, d305616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290387 q = 1) (hb : d300100 q = 1) : d305617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290387, d305617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290387, d305617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290388 q = 1) (hb : d300100 q = 1) : d305618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290388, d305618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290388, d305618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290389 q = 1) (hb : d300100 q = 1) : d305619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290389, d305619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290389, d305619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78296 (p : Pattern) (ha : d290395 p = 1) (hb : d300100 p = 1) : d305625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31716 q = 1) (hb : d300100 q = 1) : d304733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d304733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77800 q ha hb
    | true =>
      simp only [d31716, d304733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77803 q ha hb
  have h2 (q : Pattern) (ha : d31717 q = 1) (hb : d300100 q = 1) : d304734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d304734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31717, d304734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290376 q = 1) (hb : d300100 q = 1) : d305606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290376, d305606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290376, d305606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290377 q = 1) (hb : d300100 q = 1) : d305607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290377, d305607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290377, d305607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290379 q = 1) (hb : d300100 q = 1) : d305609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290379, d305609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290379, d305609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78294 q ha hb
  have h6 (q : Pattern) (ha : d290380 q = 1) (hb : d300100 q = 1) : d305610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290380, d305610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290380, d305610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290381 q = 1) (hb : d300100 q = 1) : d305611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290381, d305611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290381, d305611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290382 q = 1) (hb : d300100 q = 1) : d305612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290382, d305612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290382, d305612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290383 q = 1) (hb : d300100 q = 1) : d305613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290383, d305613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290383, d305613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290390 q = 1) (hb : d300100 q = 1) : d305620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290390, d305620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290390, d305620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78295 q ha hb
  have h11 (q : Pattern) (ha : d290391 q = 1) (hb : d300100 q = 1) : d305621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290391, d305621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290391, d305621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290392 q = 1) (hb : d300100 q = 1) : d305622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290392, d305622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290392, d305622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290393 q = 1) (hb : d300100 q = 1) : d305623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290393, d305623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290393, d305623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290394 q = 1) (hb : d300100 q = 1) : d305624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290394, d305624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290394, d305624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290395 q = 1) (hb : d300100 q = 1) : d305625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290395, d305625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290395, d305625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78297 (p : Pattern) (ha : d290401 p = 1) (hb : d300100 p = 1) : d305631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290396 q = 1) (hb : d300100 q = 1) : d305626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290396, d305626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290396, d305626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78296 q ha hb
  have h2 (q : Pattern) (ha : d290397 q = 1) (hb : d300100 q = 1) : d305627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290397, d305627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290397, d305627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290398 q = 1) (hb : d300100 q = 1) : d305628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290398, d305628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290398, d305628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290399 q = 1) (hb : d300100 q = 1) : d305629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290399, d305629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290399, d305629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290400 q = 1) (hb : d300100 q = 1) : d305630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290400, d305630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290400, d305630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290401 q = 1) (hb : d300100 q = 1) : d305631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290401, d305631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290401, d305631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78298 (p : Pattern) (ha : d290407 p = 1) (hb : d300100 p = 1) : d305637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32242 q = 1) (hb : d300100 q = 1) : d305017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77869 q ha hb
    | true =>
      simp only [d32242, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77870 q ha hb
  have h2 (q : Pattern) (ha : d32243 q = 1) (hb : d300100 q = 1) : d305018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32244 q = 1) (hb : d300100 q = 1) : d305019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32244, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32245 q = 1) (hb : d300100 q = 1) : d305020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32246 q = 1) (hb : d300100 q = 1) : d305021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290407 q = 1) (hb : d300100 q = 1) : d305637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290407, d305637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290407, d305637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78299 (p : Pattern) (ha : d290418 p = 1) (hb : d300100 p = 1) : d305648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290413 q = 1) (hb : d300100 q = 1) : d305643 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290413, d305643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77912 q ha hb
    | true =>
      simp only [d290413, d305643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77878 q ha hb
  have h2 (q : Pattern) (ha : d290414 q = 1) (hb : d300100 q = 1) : d305644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290414, d305644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290414, d305644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290415 q = 1) (hb : d300100 q = 1) : d305645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290415, d305645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290415, d305645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290416 q = 1) (hb : d300100 q = 1) : d305646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290416, d305646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290416, d305646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290417 q = 1) (hb : d300100 q = 1) : d305647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290417, d305647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290417, d305647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290418 q = 1) (hb : d300100 q = 1) : d305648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290418, d305648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290418, d305648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78300 (p : Pattern) (ha : d290424 p = 1) (hb : d300100 p = 1) : d305654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32248 q = 1) (hb : d300100 q = 1) : d305023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32248, d305023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77868 q ha hb
    | true =>
      simp only [d32248, d305023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77871 q ha hb
  have h2 (q : Pattern) (ha : d32249 q = 1) (hb : d300100 q = 1) : d305024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32249, d305024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32249, d305024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290405 q = 1) (hb : d300100 q = 1) : d305635 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290405, d305635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290405, d305635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290406 q = 1) (hb : d300100 q = 1) : d305636 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290406, d305636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290406, d305636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290408 q = 1) (hb : d300100 q = 1) : d305638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290408, d305638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290408, d305638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78298 q ha hb
  have h6 (q : Pattern) (ha : d290409 q = 1) (hb : d300100 q = 1) : d305639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290409, d305639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290409, d305639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290410 q = 1) (hb : d300100 q = 1) : d305640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290410, d305640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290410, d305640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290411 q = 1) (hb : d300100 q = 1) : d305641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290411, d305641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290411, d305641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290412 q = 1) (hb : d300100 q = 1) : d305642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290412, d305642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290412, d305642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290419 q = 1) (hb : d300100 q = 1) : d305649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290419, d305649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290419, d305649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78299 q ha hb
  have h11 (q : Pattern) (ha : d290420 q = 1) (hb : d300100 q = 1) : d305650 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290420, d305650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290420, d305650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290421 q = 1) (hb : d300100 q = 1) : d305651 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290421, d305651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290421, d305651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290422 q = 1) (hb : d300100 q = 1) : d305652 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290422, d305652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290422, d305652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290423 q = 1) (hb : d300100 q = 1) : d305653 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290423, d305653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290423, d305653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290424 q = 1) (hb : d300100 q = 1) : d305654 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290424, d305654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290424, d305654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78301 (p : Pattern) (ha : d290430 p = 1) (hb : d300100 p = 1) : d305660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290425 q = 1) (hb : d300100 q = 1) : d305655 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290425, d305655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290425, d305655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78300 q ha hb
  have h2 (q : Pattern) (ha : d290426 q = 1) (hb : d300100 q = 1) : d305656 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290426, d305656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290426, d305656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290427 q = 1) (hb : d300100 q = 1) : d305657 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290427, d305657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290427, d305657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290428 q = 1) (hb : d300100 q = 1) : d305658 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290428, d305658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290428, d305658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290429 q = 1) (hb : d300100 q = 1) : d305659 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290429, d305659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290429, d305659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290430 q = 1) (hb : d300100 q = 1) : d305660 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290430, d305660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290430, d305660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78302 (p : Pattern) (ha : d290437 p = 1) (hb : d300100 p = 1) : d305667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32776 q = 1) (hb : d300100 q = 1) : d305288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32776, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77940 q ha hb
    | true =>
      simp only [d32776, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77941 q ha hb
  have h2 (q : Pattern) (ha : d32777 q = 1) (hb : d300100 q = 1) : d305289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32777, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32777, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32778 q = 1) (hb : d300100 q = 1) : d305290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32778, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32778, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32779 q = 1) (hb : d300100 q = 1) : d305291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32779, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32779, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32780 q = 1) (hb : d300100 q = 1) : d305292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32780, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32780, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290437 q = 1) (hb : d300100 q = 1) : d305667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290437, d305667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290437, d305667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78303 (p : Pattern) (ha : d290448 p = 1) (hb : d300100 p = 1) : d305678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290443 q = 1) (hb : d300100 q = 1) : d305673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290443, d305673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77980 q ha hb
    | true =>
      simp only [d290443, d305673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77949 q ha hb
  have h2 (q : Pattern) (ha : d290444 q = 1) (hb : d300100 q = 1) : d305674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290444, d305674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290444, d305674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290445 q = 1) (hb : d300100 q = 1) : d305675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290445, d305675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290445, d305675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290446 q = 1) (hb : d300100 q = 1) : d305676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290446, d305676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290446, d305676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290447 q = 1) (hb : d300100 q = 1) : d305677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290447, d305677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290447, d305677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290448 q = 1) (hb : d300100 q = 1) : d305678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290448, d305678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290448, d305678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78304 (p : Pattern) (ha : d290454 p = 1) (hb : d300100 p = 1) : d305684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32782 q = 1) (hb : d300100 q = 1) : d305294 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32782, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77939 q ha hb
    | true =>
      simp only [d32782, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77942 q ha hb
  have h2 (q : Pattern) (ha : d32783 q = 1) (hb : d300100 q = 1) : d305295 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32783, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32783, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290435 q = 1) (hb : d300100 q = 1) : d305665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290435, d305665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290435, d305665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290436 q = 1) (hb : d300100 q = 1) : d305666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290436, d305666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290436, d305666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290438 q = 1) (hb : d300100 q = 1) : d305668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290438, d305668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290438, d305668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78302 q ha hb
  have h6 (q : Pattern) (ha : d290439 q = 1) (hb : d300100 q = 1) : d305669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290439, d305669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290439, d305669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d290440 q = 1) (hb : d300100 q = 1) : d305670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290440, d305670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290440, d305670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d290441 q = 1) (hb : d300100 q = 1) : d305671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290441, d305671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290441, d305671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d290442 q = 1) (hb : d300100 q = 1) : d305672 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290442, d305672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290442, d305672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290449 q = 1) (hb : d300100 q = 1) : d305679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290449, d305679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290449, d305679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78303 q ha hb
  have h11 (q : Pattern) (ha : d290450 q = 1) (hb : d300100 q = 1) : d305680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290450, d305680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290450, d305680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d290451 q = 1) (hb : d300100 q = 1) : d305681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290451, d305681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290451, d305681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d290452 q = 1) (hb : d300100 q = 1) : d305682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290452, d305682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290452, d305682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d290453 q = 1) (hb : d300100 q = 1) : d305683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290453, d305683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290453, d305683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d290454 q = 1) (hb : d300100 q = 1) : d305684 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290454, d305684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290454, d305684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78305 (p : Pattern) (ha : d290460 p = 1) (hb : d300100 p = 1) : d305690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290455 q = 1) (hb : d300100 q = 1) : d305685 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290455, d305685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290455, d305685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78304 q ha hb
  have h2 (q : Pattern) (ha : d290456 q = 1) (hb : d300100 q = 1) : d305686 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290456, d305686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290456, d305686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d290457 q = 1) (hb : d300100 q = 1) : d305687 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290457, d305687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290457, d305687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290458 q = 1) (hb : d300100 q = 1) : d305688 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290458, d305688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290458, d305688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290459 q = 1) (hb : d300100 q = 1) : d305689 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290459, d305689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290459, d305689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290460 q = 1) (hb : d300100 q = 1) : d305690 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290460, d305690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290460, d305690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78306 (p : Pattern) (ha : d290466 p = 1) (hb : d300100 p = 1) : d305696 p = 1 := by
  have h0 (q : Pattern) (ha : d282120 q = 1) (hb : d300100 q = 1) : d305577 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282120, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78285 q ha hb
    | true =>
      simp only [d282120, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78289 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d282147 q = 1) (hb : d300100 q = 1) : d305604 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282147, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282147, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78293 q ha hb
  have h3 (q : Pattern) (ha : d282148 q = 1) (hb : d300100 q = 1) : d305605 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d282148, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282148, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d290402 q = 1) (hb : d300100 q = 1) : d305632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290402, d305632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290402, d305632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78297 q ha hb
  have h5 (q : Pattern) (ha : d290403 q = 1) (hb : d300100 q = 1) : d305633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290403, d305633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290403, d305633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290404 q = 1) (hb : d300100 q = 1) : d305634 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290404, d305634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290404, d305634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290431 q = 1) (hb : d300100 q = 1) : d305661 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290431, d305661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290431, d305661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78301 q ha hb
  have h8 (q : Pattern) (ha : d290432 q = 1) (hb : d300100 q = 1) : d305662 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290432, d305662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290432, d305662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d290433 q = 1) (hb : d300100 q = 1) : d305663 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290433, d305663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290433, d305663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290434 q = 1) (hb : d300100 q = 1) : d305664 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290434, d305664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290434, d305664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d290461 q = 1) (hb : d300100 q = 1) : d305691 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290461, d305691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290461, d305691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78305 q ha hb
  have h12 (q : Pattern) (ha : d290462 q = 1) (hb : d300100 q = 1) : d305692 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290462, d305692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290462, d305692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d290463 q = 1) (hb : d300100 q = 1) : d305693 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290463, d305693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290463, d305693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d290464 q = 1) (hb : d300100 q = 1) : d305694 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290464, d305694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290464, d305694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d290465 q = 1) (hb : d300100 q = 1) : d305695 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290465, d305695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290465, d305695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d290466 q = 1) (hb : d300100 q = 1) : d305696 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290466, d305696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290466, d305696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro78307 (p : Pattern) (ha : d290472 p = 1) (hb : d300100 p = 1) : d305702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290467 q = 1) (hb : d300100 q = 1) : d305697 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290467, d305697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78306 q ha hb
    | true =>
      simp only [d290467, d305697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290468 q = 1) (hb : d300100 q = 1) : d305698 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290468, d305698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290468, d305698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290469 q = 1) (hb : d300100 q = 1) : d305699 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290469, d305699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290469, d305699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290470 q = 1) (hb : d300100 q = 1) : d305700 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290470, d305700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290470, d305700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290471 q = 1) (hb : d300100 q = 1) : d305701 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290471, d305701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290471, d305701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290472 q = 1) (hb : d300100 q = 1) : d305702 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290472, d305702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290472, d305702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78308 (p : Pattern) (ha : d290478 p = 1) (hb : d300100 p = 1) : d305708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290473 q = 1) (hb : d300100 q = 1) : d305703 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290473, d305703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78307 q ha hb
    | true =>
      simp only [d290473, d305703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290474 q = 1) (hb : d300100 q = 1) : d305704 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290474, d305704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290474, d305704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290475 q = 1) (hb : d300100 q = 1) : d305705 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290475, d305705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290475, d305705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290476 q = 1) (hb : d300100 q = 1) : d305706 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290476, d305706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290476, d305706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290477 q = 1) (hb : d300100 q = 1) : d305707 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290477, d305707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290477, d305707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290478 q = 1) (hb : d300100 q = 1) : d305708 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290478, d305708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290478, d305708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78309 (p : Pattern) (ha : d290484 p = 1) (hb : d300100 p = 1) : d305714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290479 q = 1) (hb : d300100 q = 1) : d305709 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290479, d305709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78308 q ha hb
    | true =>
      simp only [d290479, d305709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290480 q = 1) (hb : d300100 q = 1) : d305710 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290480, d305710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290480, d305710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290481 q = 1) (hb : d300100 q = 1) : d305711 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290481, d305711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290481, d305711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290482 q = 1) (hb : d300100 q = 1) : d305712 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290482, d305712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290482, d305712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290483 q = 1) (hb : d300100 q = 1) : d305713 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290483, d305713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290483, d305713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290484 q = 1) (hb : d300100 q = 1) : d305714 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290484, d305714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290484, d305714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78310 (p : Pattern) (ha : d290490 p = 1) (hb : d300100 p = 1) : d305720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290485 q = 1) (hb : d300100 q = 1) : d305715 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290485, d305715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78309 q ha hb
    | true =>
      simp only [d290485, d305715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290486 q = 1) (hb : d300100 q = 1) : d305716 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290486, d305716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290486, d305716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290487 q = 1) (hb : d300100 q = 1) : d305717 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290487, d305717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290487, d305717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290488 q = 1) (hb : d300100 q = 1) : d305718 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290488, d305718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290488, d305718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290489 q = 1) (hb : d300100 q = 1) : d305719 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290489, d305719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290489, d305719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290490 q = 1) (hb : d300100 q = 1) : d305720 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290490, d305720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290490, d305720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78311 (p : Pattern) (ha : d290496 p = 1) (hb : d300100 p = 1) : d305726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290491 q = 1) (hb : d300100 q = 1) : d305721 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290491, d305721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78310 q ha hb
    | true =>
      simp only [d290491, d305721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290492 q = 1) (hb : d300100 q = 1) : d305722 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290492, d305722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290492, d305722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290493 q = 1) (hb : d300100 q = 1) : d305723 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290493, d305723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290493, d305723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290494 q = 1) (hb : d300100 q = 1) : d305724 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290494, d305724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290494, d305724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290495 q = 1) (hb : d300100 q = 1) : d305725 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290495, d305725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290495, d305725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290496 q = 1) (hb : d300100 q = 1) : d305726 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290496, d305726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290496, d305726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78312 (p : Pattern) (ha : d290502 p = 1) (hb : d300100 p = 1) : d305732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290497 q = 1) (hb : d300100 q = 1) : d305727 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290497, d305727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78311 q ha hb
    | true =>
      simp only [d290497, d305727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290498 q = 1) (hb : d300100 q = 1) : d305728 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290498, d305728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290498, d305728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290499 q = 1) (hb : d300100 q = 1) : d305729 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290499, d305729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290499, d305729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290500 q = 1) (hb : d300100 q = 1) : d305730 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290500, d305730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290500, d305730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290501 q = 1) (hb : d300100 q = 1) : d305731 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290501, d305731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290501, d305731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290502 q = 1) (hb : d300100 q = 1) : d305732 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290502, d305732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290502, d305732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78313 (p : Pattern) (ha : d290508 p = 1) (hb : d300100 p = 1) : d305738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d290503 q = 1) (hb : d300100 q = 1) : d305733 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290503, d305733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78312 q ha hb
    | true =>
      simp only [d290503, d305733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d290504 q = 1) (hb : d300100 q = 1) : d305734 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290504, d305734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290504, d305734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d290505 q = 1) (hb : d300100 q = 1) : d305735 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290505, d305735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290505, d305735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d290506 q = 1) (hb : d300100 q = 1) : d305736 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290506, d305736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290506, d305736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d290507 q = 1) (hb : d300100 q = 1) : d305737 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290507, d305737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290507, d305737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d290508 q = 1) (hb : d300100 q = 1) : d305738 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290508, d305738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290508, d305738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78314 (p : Pattern) (ha : d302649 p = 1) (hb : d304159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d302644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302534 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302534, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78000 q ha hb
    | true =>
      simp only [d302534, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d302645 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302645, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d302645, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d302535 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d302646 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302646, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302646, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d302647 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302647, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302647, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d302648 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302648, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302648, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d302649 q = 1) (hb : d304159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302649, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302649, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78315 (p : Pattern) (ha : d302665 p = 1) (hb : d304166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302534 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302534, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78000 q ha hb
    | true =>
      simp only [d302534, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d302645 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302645, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302645, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d302535 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d302646 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302646, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302646, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d302647 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302647, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302647, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d302648 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302648, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302648, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d302654 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d302658 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d302660 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d302541 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302541, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78002 q ha hb
    | true =>
      simp only [d302541, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d302661 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302661, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d302661, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d302542 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d302662 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302662, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d302662, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d302663 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302663, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d302663, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d302664 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302664, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d302664, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d302665 q = 1) (hb : d304166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302665, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d302665, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78316 (p : Pattern) (ha : d302674 p = 1) (hb : d304381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302660 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302541 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302541, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78002 q ha hb
    | true =>
      simp only [d302541, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d302661 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302661, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302661, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302542 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302662 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302662, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302662, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302672 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302672, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302672, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302673 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302673, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302673, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302674 q = 1) (hb : d304381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302674, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302674, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78317 (p : Pattern) (ha : d302703 p = 1) (hb : d304427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302698 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302575 q = 1) (hb : d304138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302575, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78007 q ha hb
    | true =>
      simp only [d302575, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d302699 q = 1) (hb : d304423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302699, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302699, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302576 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302700 q = 1) (hb : d304424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302700, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302700, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302701 q = 1) (hb : d304425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302701, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302701, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302702 q = 1) (hb : d304426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302702, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302702, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302703 q = 1) (hb : d304427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302703, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302703, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78318 (p : Pattern) (ha : d302709 p = 1) (hb : d305545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d302666 q = 1) (hb : d304167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302666, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78314 q ha hb
    | true =>
      simp only [d302666, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78315 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302668 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d302669 q = 1) (hb : d304168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302669, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d302669, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302670 q = 1) (hb : d305535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302670, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302670, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302671 q = 1) (hb : d305536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302671, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302671, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302675 q = 1) (hb : d304382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302675, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d302675, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78316 q ha hb
  have h8 (q : Pattern) (ha : d302676 q = 1) (hb : d305537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302676, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d302676, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d302677 q = 1) (hb : d305538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302677, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d302677, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d302678 q = 1) (hb : d305539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302678, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d302678, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d302679 q = 1) (hb : d305540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302679, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302679, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d302704 q = 1) (hb : d304428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302704, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d302704, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78317 q ha hb
  have h13 (q : Pattern) (ha : d302705 q = 1) (hb : d305541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302705, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d302705, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d302706 q = 1) (hb : d305542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302706, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d302706, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d302707 q = 1) (hb : d305543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302707, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d302707, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d302708 q = 1) (hb : d305544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302708, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d302708, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d302709 q = 1) (hb : d305545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d302709, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d302709, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro78319 (p : Pattern) (ha : d302715 p = 1) (hb : d305551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302591 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302710 q = 1) (hb : d305546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d302710, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302710, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78318 q ha hb
  have h3 (q : Pattern) (ha : d302711 q = 1) (hb : d305547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d302711, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302711, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d302712 q = 1) (hb : d305548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d302712, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302712, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d302713 q = 1) (hb : d305549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d302713, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302713, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302714 q = 1) (hb : d305550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d302714, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302714, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302715 q = 1) (hb : d305551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d302715, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302715, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro78320 (p : Pattern) (ha : d302791 p = 1) (hb : d304284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302742 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d302780 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302644 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302644, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78018 q ha hb
    | true =>
      simp only [d302644, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78000 q ha hb
  have h5 (q : Pattern) (ha : d302781 q = 1) (hb : d304280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302781, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d302781, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d302787 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d302788 q = 1) (hb : d304281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302788, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302788, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d302789 q = 1) (hb : d304282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302789, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302789, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d302790 q = 1) (hb : d304283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302790, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302790, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d302791 q = 1) (hb : d304284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302791, d304284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302791, d304284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78321 (p : Pattern) (ha : d302810 p = 1) (hb : d304291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302736 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302742 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302780 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d302644 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302644, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78018 q ha hb
    | true =>
      simp only [d302644, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78000 q ha hb
  have h4 (q : Pattern) (ha : d302781 q = 1) (hb : d304280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302781, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302781, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d302787 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d302788 q = 1) (hb : d304281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302788, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d302788, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d302789 q = 1) (hb : d304282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302789, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302789, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302790 q = 1) (hb : d304283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302790, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302790, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d302796 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d302800 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d302802 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d302660 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302660, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78022 q ha hb
    | true =>
      simp only [d302660, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78002 q ha hb
  have h13 (q : Pattern) (ha : d302803 q = 1) (hb : d304287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302803, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d302803, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d302806 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d302807 q = 1) (hb : d304288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302807, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d302807, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d302808 q = 1) (hb : d304289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302808, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d302808, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d302809 q = 1) (hb : d304290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302809, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d302809, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d302810 q = 1) (hb : d304291 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302810, d304291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d302810, d304291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78322 (p : Pattern) (ha : d302819 p = 1) (hb : d305554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302802 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302660 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302660, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78022 q ha hb
    | true =>
      simp only [d302660, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78002 q ha hb
  have h3 (q : Pattern) (ha : d302803 q = 1) (hb : d304287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302803, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302803, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302806 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302807 q = 1) (hb : d304288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302807, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302807, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302817 q = 1) (hb : d304289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302817, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302817, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302818 q = 1) (hb : d304290 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302818, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302818, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302819 q = 1) (hb : d305554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302819, d305554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302819, d305554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78323 (p : Pattern) (ha : d302861 p = 1) (hb : d305564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302850 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302698 q = 1) (hb : d304262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302698, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78028 q ha hb
    | true =>
      simp only [d302698, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78007 q ha hb
  have h3 (q : Pattern) (ha : d302851 q = 1) (hb : d305560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302851, d305560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302851, d305560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302858 q = 1) (hb : d305561 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302858, d305561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302858, d305561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302859 q = 1) (hb : d305562 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302859, d305562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302859, d305562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302860 q = 1) (hb : d305563 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302860, d305563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302860, d305563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302861 q = 1) (hb : d305564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302861, d305564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302861, d305564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78324 (p : Pattern) (ha : d302873 p = 1) (hb : d305570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d302811 q = 1) (hb : d304292 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302811, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78320 q ha hb
    | true =>
      simp only [d302811, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78321 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d302814 q = 1) (hb : d304293 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302814, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d302814, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302815 q = 1) (hb : d305552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302815, d305552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302815, d305552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d302816 q = 1) (hb : d305553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302816, d305553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302816, d305553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302820 q = 1) (hb : d305555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302820, d305555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d302820, d305555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78322 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d302822 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d302823 q = 1) (hb : d305556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302823, d305556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d302823, d305556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d302824 q = 1) (hb : d305557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302824, d305557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d302824, d305557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d302825 q = 1) (hb : d305558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302825, d305558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d302825, d305558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d302826 q = 1) (hb : d305559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302826, d305559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302826, d305559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d302862 q = 1) (hb : d305565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302862, d305565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d302862, d305565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78323 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d302868 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d302869 q = 1) (hb : d305566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302869, d305566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d302869, d305566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d302870 q = 1) (hb : d305567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302870, d305567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d302870, d305567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d302871 q = 1) (hb : d305568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302871, d305568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d302871, d305568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d302872 q = 1) (hb : d305569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302872, d305569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d302872, d305569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d302873 q = 1) (hb : d305570 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d302873, d305570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d302873, d305570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78325 (p : Pattern) (ha : d302879 p = 1) (hb : d305576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d302874 q = 1) (hb : d305571 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d302874, d305571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302874, d305571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78324 q ha hb
  have h2 (q : Pattern) (ha : d302875 q = 1) (hb : d305572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d302875, d305572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302875, d305572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d302876 q = 1) (hb : d305573 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d302876, d305573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302876, d305573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d302877 q = 1) (hb : d305574 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d302877, d305574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302877, d305574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d302878 q = 1) (hb : d305575 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d302878, d305575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302878, d305575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302879 q = 1) (hb : d305576 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d302879, d305576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302879, d305576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78326 (p : Pattern) (ha : d302994 p = 1) (hb : d304463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d302983 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302898 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302898, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78063 q ha hb
    | true =>
      simp only [d302898, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78064 q ha hb
  have h5 (q : Pattern) (ha : d302984 q = 1) (hb : d304459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302984, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d302984, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d302990 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d302991 q = 1) (hb : d304460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302991, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302991, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d302992 q = 1) (hb : d304461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302992, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302992, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d302993 q = 1) (hb : d304462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302993, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302993, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d302994 q = 1) (hb : d304463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302994, d304463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302994, d304463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78327 (p : Pattern) (ha : d303015 p = 1) (hb : d304473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302983 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d302898 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302898, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78063 q ha hb
    | true =>
      simp only [d302898, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78064 q ha hb
  have h4 (q : Pattern) (ha : d302984 q = 1) (hb : d304459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302984, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d302984, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d302990 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d302991 q = 1) (hb : d304460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302991, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d302991, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d302992 q = 1) (hb : d304461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302992, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d302992, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d302993 q = 1) (hb : d304462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302993, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d302993, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d303000 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d303005 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d303007 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d302908 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302908, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78066 q ha hb
    | true =>
      simp only [d302908, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78067 q ha hb
  have h13 (q : Pattern) (ha : d303008 q = 1) (hb : d304469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303008, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d303008, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303011 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303012 q = 1) (hb : d304470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303012, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303012, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303013 q = 1) (hb : d304471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303013, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d303013, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d303014 q = 1) (hb : d304472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303014, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d303014, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d303015 q = 1) (hb : d304473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303015, d304473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303015, d304473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78328 (p : Pattern) (ha : d303035 p = 1) (hb : d305580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d302908 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302908, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78066 q ha hb
    | true =>
      simp only [d302908, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78067 q ha hb
  have h3 (q : Pattern) (ha : d303008 q = 1) (hb : d304469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303008, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303008, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303012 q = 1) (hb : d304470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303012, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303012, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303033 q = 1) (hb : d304471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303033, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303033, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303034 q = 1) (hb : d304472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303034, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303034, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303035 q = 1) (hb : d305580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303035, d305580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303035, d305580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78329 (p : Pattern) (ha : d303103 p = 1) (hb : d305591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303087 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303092 q = 1) (hb : d305586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303092, d305586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78101 q ha hb
    | true =>
      simp only [d303092, d305586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78104 q ha hb
  have h3 (q : Pattern) (ha : d303093 q = 1) (hb : d305587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303093, d305587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303093, d305587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303100 q = 1) (hb : d305588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303100, d305588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303100, d305588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303101 q = 1) (hb : d305589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303101, d305589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303101, d305589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303102 q = 1) (hb : d305590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303102, d305590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303102, d305590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303103 q = 1) (hb : d305591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303103, d305591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303103, d305591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78330 (p : Pattern) (ha : d303116 p = 1) (hb : d305597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302916 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303016 q = 1) (hb : d304474 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303016, d304474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78326 q ha hb
    | true =>
      simp only [d303016, d304474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78327 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303029 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303030 q = 1) (hb : d304475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303030, d304475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303030, d304475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303031 q = 1) (hb : d305578 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303031, d305578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303031, d305578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303032 q = 1) (hb : d305579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303032, d305579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303032, d305579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303036 q = 1) (hb : d305581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303036, d305581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303036, d305581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78328 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303038 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303039 q = 1) (hb : d305582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303039, d305582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303039, d305582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d303040 q = 1) (hb : d305583 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303040, d305583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303040, d305583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d303041 q = 1) (hb : d305584 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303041, d305584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303041, d305584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d303042 q = 1) (hb : d305585 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303042, d305585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303042, d305585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d303104 q = 1) (hb : d305592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303104, d305592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303104, d305592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78329 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303111 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303112 q = 1) (hb : d305593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303112, d305593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303112, d305593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303113 q = 1) (hb : d305594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303113, d305594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d303113, d305594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d303114 q = 1) (hb : d305595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303114, d305595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d303114, d305595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d303115 q = 1) (hb : d305596 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303115, d305596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d303115, d305596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d303116 q = 1) (hb : d305597 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d303116, d305597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303116, d305597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78331 (p : Pattern) (ha : d303122 p = 1) (hb : d305603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303117 q = 1) (hb : d305598 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d303117, d305598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303117, d305598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78330 q ha hb
  have h2 (q : Pattern) (ha : d303118 q = 1) (hb : d305599 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d303118, d305599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303118, d305599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303119 q = 1) (hb : d305600 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d303119, d305600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303119, d305600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303120 q = 1) (hb : d305601 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d303120, d305601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303120, d305601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303121 q = 1) (hb : d305602 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d303121, d305602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303121, d305602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303122 q = 1) (hb : d305603 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d303122, d305603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303122, d305603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78332 (p : Pattern) (ha : d303246 p = 1) (hb : d304722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303186 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303195 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d303235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d303160 q = 1) (hb : d304717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303160, d304717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78114 q ha hb
    | true =>
      simp only [d303160, d304717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78115 q ha hb
  have h5 (q : Pattern) (ha : d303236 q = 1) (hb : d304718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303236, d304718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d303236, d304718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d303242 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d303243 q = 1) (hb : d304719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303243, d304719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303243, d304719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d303244 q = 1) (hb : d304720 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303244, d304720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303244, d304720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303245 q = 1) (hb : d304721 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303245, d304721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303245, d304721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303246 q = 1) (hb : d304722 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303246, d304722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303246, d304722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78333 (p : Pattern) (ha : d303267 p = 1) (hb : d304732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303186 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303195 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303235 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303160 q = 1) (hb : d304717 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303160, d304717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78114 q ha hb
    | true =>
      simp only [d303160, d304717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78115 q ha hb
  have h4 (q : Pattern) (ha : d303236 q = 1) (hb : d304718 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303236, d304718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303236, d304718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d303242 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d303243 q = 1) (hb : d304719 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303243, d304719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303243, d304719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d303244 q = 1) (hb : d304720 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303244, d304720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303244, d304720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303245 q = 1) (hb : d304721 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303245, d304721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303245, d304721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d303252 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d303257 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d303259 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d303170 q = 1) (hb : d304727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303170, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78117 q ha hb
    | true =>
      simp only [d303170, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78118 q ha hb
  have h13 (q : Pattern) (ha : d303260 q = 1) (hb : d304728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303260, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d303260, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303263 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303264 q = 1) (hb : d304729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303264, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303264, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303265 q = 1) (hb : d304730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303265, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d303265, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d303266 q = 1) (hb : d304731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303266, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d303266, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d303267 q = 1) (hb : d304732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303267, d304732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303267, d304732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78334 (p : Pattern) (ha : d303287 p = 1) (hb : d305608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303259 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303170 q = 1) (hb : d304727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303170, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78117 q ha hb
    | true =>
      simp only [d303170, d304727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78118 q ha hb
  have h3 (q : Pattern) (ha : d303260 q = 1) (hb : d304728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303260, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303260, d304728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303264 q = 1) (hb : d304729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303264, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303264, d304729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303285 q = 1) (hb : d304730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303285, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303285, d304730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303286 q = 1) (hb : d304731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303286, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303286, d304731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303287 q = 1) (hb : d305608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303287, d305608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303287, d305608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78335 (p : Pattern) (ha : d303372 p = 1) (hb : d305619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303356 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303361 q = 1) (hb : d305614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303361, d305614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78153 q ha hb
    | true =>
      simp only [d303361, d305614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78156 q ha hb
  have h3 (q : Pattern) (ha : d303362 q = 1) (hb : d305615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303362, d305615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303362, d305615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303368 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303369 q = 1) (hb : d305616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303369, d305616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303369, d305616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303370 q = 1) (hb : d305617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303370, d305617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303370, d305617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303371 q = 1) (hb : d305618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303371, d305618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303371, d305618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303372 q = 1) (hb : d305619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303372, d305619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303372, d305619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78336 (p : Pattern) (ha : d303385 p = 1) (hb : d305625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303268 q = 1) (hb : d304733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303268, d304733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78332 q ha hb
    | true =>
      simp only [d303268, d304733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78333 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303282 q = 1) (hb : d304734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303282, d304734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303282, d304734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303283 q = 1) (hb : d305606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303283, d305606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303283, d305606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303284 q = 1) (hb : d305607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303284, d305607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303284, d305607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303288 q = 1) (hb : d305609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303288, d305609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303288, d305609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78334 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303290 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303291 q = 1) (hb : d305610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303291, d305610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303291, d305610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d303292 q = 1) (hb : d305611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303292, d305611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303292, d305611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d303293 q = 1) (hb : d305612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303293, d305612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303293, d305612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d303294 q = 1) (hb : d305613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303294, d305613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303294, d305613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d303373 q = 1) (hb : d305620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303373, d305620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303373, d305620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78335 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303380 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303381 q = 1) (hb : d305621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303381, d305621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303381, d305621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303382 q = 1) (hb : d305622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303382, d305622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d303382, d305622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d303383 q = 1) (hb : d305623 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303383, d305623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d303383, d305623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d303384 q = 1) (hb : d305624 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303384, d305624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d303384, d305624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d303385 q = 1) (hb : d305625 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d303385, d305625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303385, d305625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78337 (p : Pattern) (ha : d303391 p = 1) (hb : d305631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303386 q = 1) (hb : d305626 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d303386, d305626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303386, d305626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78336 q ha hb
  have h2 (q : Pattern) (ha : d303387 q = 1) (hb : d305627 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d303387, d305627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303387, d305627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303388 q = 1) (hb : d305628 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d303388, d305628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303388, d305628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303389 q = 1) (hb : d305629 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d303389, d305629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303389, d305629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303390 q = 1) (hb : d305630 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d303390, d305630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303390, d305630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303391 q = 1) (hb : d305631 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d303391, d305631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303391, d305631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78338 (p : Pattern) (ha : d303553 p = 1) (hb : d305012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303501 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d303526 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d303466 q = 1) (hb : d305007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303466, d305007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78169 q ha hb
    | true =>
      simp only [d303466, d305007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78170 q ha hb
  have h5 (q : Pattern) (ha : d303527 q = 1) (hb : d305008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303527, d305008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d303527, d305008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d303549 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d303550 q = 1) (hb : d305009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303550, d305009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303550, d305009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d303551 q = 1) (hb : d305010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303551, d305010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303551, d305010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303552 q = 1) (hb : d305011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303552, d305011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303552, d305011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303553 q = 1) (hb : d305012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303553, d305012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303553, d305012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78339 (p : Pattern) (ha : d303574 p = 1) (hb : d305022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303526 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303466 q = 1) (hb : d305007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303466, d305007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78169 q ha hb
    | true =>
      simp only [d303466, d305007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78170 q ha hb
  have h4 (q : Pattern) (ha : d303527 q = 1) (hb : d305008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303527, d305008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303527, d305008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d303549 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d303550 q = 1) (hb : d305009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303550, d305009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303550, d305009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d303551 q = 1) (hb : d305010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303551, d305010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303551, d305010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303552 q = 1) (hb : d305011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303552, d305011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303552, d305011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d303559 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d303564 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d303566 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d303476 q = 1) (hb : d305017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303476, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78172 q ha hb
    | true =>
      simp only [d303476, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78173 q ha hb
  have h13 (q : Pattern) (ha : d303567 q = 1) (hb : d305018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303567, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d303567, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303570 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303571 q = 1) (hb : d305019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303571, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303571, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303572 q = 1) (hb : d305020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303572, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d303572, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d303573 q = 1) (hb : d305021 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303573, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d303573, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d303574 q = 1) (hb : d305022 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303574, d305022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303574, d305022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78340 (p : Pattern) (ha : d303594 p = 1) (hb : d305637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303476 q = 1) (hb : d305017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303476, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78172 q ha hb
    | true =>
      simp only [d303476, d305017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78173 q ha hb
  have h3 (q : Pattern) (ha : d303567 q = 1) (hb : d305018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303567, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303567, d305018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303570 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303571 q = 1) (hb : d305019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303571, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303571, d305019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303592 q = 1) (hb : d305020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303592, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303592, d305020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303593 q = 1) (hb : d305021 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303593, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303593, d305021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303594 q = 1) (hb : d305637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303594, d305637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303594, d305637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78341 (p : Pattern) (ha : d303704 p = 1) (hb : d305648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303673 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303678 q = 1) (hb : d305643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303678, d305643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78210 q ha hb
    | true =>
      simp only [d303678, d305643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78216 q ha hb
  have h3 (q : Pattern) (ha : d303679 q = 1) (hb : d305644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303679, d305644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303679, d305644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303700 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303701 q = 1) (hb : d305645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303701, d305645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303701, d305645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303702 q = 1) (hb : d305646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303702, d305646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303702, d305646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303703 q = 1) (hb : d305647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303703, d305647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303703, d305647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303704 q = 1) (hb : d305648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303704, d305648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303704, d305648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78342 (p : Pattern) (ha : d303717 p = 1) (hb : d305654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303575 q = 1) (hb : d305023 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303575, d305023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78338 q ha hb
    | true =>
      simp only [d303575, d305023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78339 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303589 q = 1) (hb : d305024 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303589, d305024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303589, d305024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303590 q = 1) (hb : d305635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303590, d305635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303590, d305635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303591 q = 1) (hb : d305636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303591, d305636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303591, d305636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303595 q = 1) (hb : d305638 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303595, d305638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303595, d305638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78340 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303597 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303598 q = 1) (hb : d305639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303598, d305639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303598, d305639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d303599 q = 1) (hb : d305640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303599, d305640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303599, d305640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d303600 q = 1) (hb : d305641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303600, d305641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303600, d305641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d303601 q = 1) (hb : d305642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303601, d305642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303601, d305642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d303705 q = 1) (hb : d305649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303705, d305649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303705, d305649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78341 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303712 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303713 q = 1) (hb : d305650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303713, d305650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303713, d305650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303714 q = 1) (hb : d305651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303714, d305651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d303714, d305651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d303715 q = 1) (hb : d305652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303715, d305652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d303715, d305652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d303716 q = 1) (hb : d305653 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303716, d305653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d303716, d305653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d303717 q = 1) (hb : d305654 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d303717, d305654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d303717, d305654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78343 (p : Pattern) (ha : d303723 p = 1) (hb : d305660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303718 q = 1) (hb : d305655 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d303718, d305655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303718, d305655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78342 q ha hb
  have h2 (q : Pattern) (ha : d303719 q = 1) (hb : d305656 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d303719, d305656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303719, d305656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d303720 q = 1) (hb : d305657 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d303720, d305657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303720, d305657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303721 q = 1) (hb : d305658 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d303721, d305658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303721, d305658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d303722 q = 1) (hb : d305659 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d303722, d305659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303722, d305659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303723 q = 1) (hb : d305660 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d303723, d305660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303723, d305660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78344 (p : Pattern) (ha : d303871 p = 1) (hb : d305283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d303841 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d303792 q = 1) (hb : d305278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78228 q ha hb
    | true =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78229 q ha hb
  have h5 (q : Pattern) (ha : d303842 q = 1) (hb : d305279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303842, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d303842, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d303867 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d303868 q = 1) (hb : d305280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303868, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d303868, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d303869 q = 1) (hb : d305281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303869, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303869, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303870 q = 1) (hb : d305282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303870, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303870, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303871 q = 1) (hb : d305283 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303871, d305283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303871, d305283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78345 (p : Pattern) (ha : d303892 p = 1) (hb : d305293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303818 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303827 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303841 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303792 q = 1) (hb : d305278 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78228 q ha hb
    | true =>
      simp only [d303792, d305278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78229 q ha hb
  have h4 (q : Pattern) (ha : d303842 q = 1) (hb : d305279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303842, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d303842, d305279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d303867 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d303868 q = 1) (hb : d305280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303868, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d303868, d305280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d303869 q = 1) (hb : d305281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303869, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303869, d305281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303870 q = 1) (hb : d305282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303870, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303870, d305282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d303877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d303882 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d303884 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d303802 q = 1) (hb : d305288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303802, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78231 q ha hb
    | true =>
      simp only [d303802, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78232 q ha hb
  have h13 (q : Pattern) (ha : d303885 q = 1) (hb : d305289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303885, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d303885, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d303888 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d303889 q = 1) (hb : d305290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303889, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d303889, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d303890 q = 1) (hb : d305291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303890, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d303890, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d303891 q = 1) (hb : d305292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303891, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d303891, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d303892 q = 1) (hb : d305293 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303892, d305293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d303892, d305293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78346 (p : Pattern) (ha : d303912 p = 1) (hb : d305667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303802 q = 1) (hb : d305288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303802, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78231 q ha hb
    | true =>
      simp only [d303802, d305288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78232 q ha hb
  have h3 (q : Pattern) (ha : d303885 q = 1) (hb : d305289 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303885, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303885, d305289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303888 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303889 q = 1) (hb : d305290 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d303889, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303889, d305290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303910 q = 1) (hb : d305291 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d303910, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303910, d305291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303911 q = 1) (hb : d305292 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d303911, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303911, d305292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d303912 q = 1) (hb : d305667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d303912, d305667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303912, d305667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78347 (p : Pattern) (ha : d304003 p = 1) (hb : d305678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d303972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303977 q = 1) (hb : d305673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d303977, d305673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78264 q ha hb
    | true =>
      simp only [d303977, d305673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78269 q ha hb
  have h3 (q : Pattern) (ha : d303978 q = 1) (hb : d305674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d303978, d305674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303978, d305674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d303999 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304000 q = 1) (hb : d305675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304000, d305675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304000, d305675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d304001 q = 1) (hb : d305676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304001, d305676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304001, d305676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304002 q = 1) (hb : d305677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304002, d305677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304002, d305677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304003 q = 1) (hb : d305678 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304003, d305678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304003, d305678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78348 (p : Pattern) (ha : d304016 p = 1) (hb : d305684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d303810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d303893 q = 1) (hb : d305294 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303893, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78344 q ha hb
    | true =>
      simp only [d303893, d305294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78345 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d303906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d303907 q = 1) (hb : d305295 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303907, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d303907, d305295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d303908 q = 1) (hb : d305665 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303908, d305665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303908, d305665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d303909 q = 1) (hb : d305666 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303909, d305666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d303909, d305666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303913 q = 1) (hb : d305668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d303913, d305668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d303913, d305668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78346 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d303915 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d303916 q = 1) (hb : d305669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d303916, d305669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d303916, d305669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d303917 q = 1) (hb : d305670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d303917, d305670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d303917, d305670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d303918 q = 1) (hb : d305671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d303918, d305671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d303918, d305671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d303919 q = 1) (hb : d305672 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d303919, d305672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303919, d305672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d304004 q = 1) (hb : d305679 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304004, d305679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d304004, d305679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78347 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d304011 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304012 q = 1) (hb : d305680 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304012, d305680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304012, d305680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d304013 q = 1) (hb : d305681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d304013, d305681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d304013, d305681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d304014 q = 1) (hb : d305682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d304014, d305682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d304014, d305682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d304015 q = 1) (hb : d305683 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d304015, d305683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d304015, d305683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d304016 q = 1) (hb : d305684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d304016, d305684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d304016, d305684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78349 (p : Pattern) (ha : d304022 p = 1) (hb : d305690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304017 q = 1) (hb : d305685 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d304017, d305685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304017, d305685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78348 q ha hb
  have h2 (q : Pattern) (ha : d304018 q = 1) (hb : d305686 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d304018, d305686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304018, d305686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d304019 q = 1) (hb : d305687 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d304019, d305687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304019, d305687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d304020 q = 1) (hb : d305688 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d304020, d305688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304020, d305688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304021 q = 1) (hb : d305689 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d304021, d305689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304021, d305689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304022 q = 1) (hb : d305690 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d304022, d305690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d304022, d305690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78350 (p : Pattern) (ha : d304028 p = 1) (hb : d305696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d302880 q = 1) (hb : d305577 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d302880, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78319 q ha hb
    | true =>
      simp only [d302880, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78325 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d303123 q = 1) (hb : d305604 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303123, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303123, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78331 q ha hb
  have h3 (q : Pattern) (ha : d303124 q = 1) (hb : d305605 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303124, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303124, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d303392 q = 1) (hb : d305632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303392, d305632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303392, d305632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78337 q ha hb
  have h5 (q : Pattern) (ha : d303393 q = 1) (hb : d305633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303393, d305633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303393, d305633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303394 q = 1) (hb : d305634 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d303394, d305634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d303394, d305634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d303724 q = 1) (hb : d305661 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d303724, d305661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303724, d305661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78343 q ha hb
  have h8 (q : Pattern) (ha : d303725 q = 1) (hb : d305662 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d303725, d305662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303725, d305662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d303726 q = 1) (hb : d305663 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d303726, d305663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d303726, d305663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d303727 q = 1) (hb : d305664 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d303727, d305664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d303727, d305664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d304023 q = 1) (hb : d305691 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d304023, d305691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304023, d305691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78349 q ha hb
  have h12 (q : Pattern) (ha : d304024 q = 1) (hb : d305692 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d304024, d305692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304024, d305692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d304025 q = 1) (hb : d305693 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d304025, d305693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304025, d305693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d304026 q = 1) (hb : d305694 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d304026, d305694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d304026, d305694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d304027 q = 1) (hb : d305695 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d304027, d305695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304027, d305695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304028 q = 1) (hb : d305696 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d304028, d305696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d304028, d305696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro78351 (p : Pattern) (ha : d304034 p = 1) (hb : d305702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304029 q = 1) (hb : d305697 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d304029, d305697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78350 q ha hb
    | true =>
      simp only [d304029, d305697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304030 q = 1) (hb : d305698 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d304030, d305698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304030, d305698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304031 q = 1) (hb : d305699 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d304031, d305699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304031, d305699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304032 q = 1) (hb : d305700 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d304032, d305700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304032, d305700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304033 q = 1) (hb : d305701 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d304033, d305701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304033, d305701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304034 q = 1) (hb : d305702 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d304034, d305702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304034, d305702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78352 (p : Pattern) (ha : d304040 p = 1) (hb : d305708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304035 q = 1) (hb : d305703 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d304035, d305703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78351 q ha hb
    | true =>
      simp only [d304035, d305703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304036 q = 1) (hb : d305704 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d304036, d305704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304036, d305704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304037 q = 1) (hb : d305705 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d304037, d305705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304037, d305705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304038 q = 1) (hb : d305706 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d304038, d305706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304038, d305706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304039 q = 1) (hb : d305707 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d304039, d305707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304039, d305707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304040 q = 1) (hb : d305708 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d304040, d305708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304040, d305708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78353 (p : Pattern) (ha : d304046 p = 1) (hb : d305714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304041 q = 1) (hb : d305709 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d304041, d305709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78352 q ha hb
    | true =>
      simp only [d304041, d305709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304042 q = 1) (hb : d305710 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d304042, d305710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304042, d305710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304043 q = 1) (hb : d305711 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d304043, d305711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304043, d305711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304044 q = 1) (hb : d305712 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d304044, d305712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304044, d305712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304045 q = 1) (hb : d305713 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d304045, d305713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304045, d305713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304046 q = 1) (hb : d305714 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d304046, d305714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304046, d305714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78354 (p : Pattern) (ha : d304052 p = 1) (hb : d305720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304047 q = 1) (hb : d305715 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d304047, d305715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78353 q ha hb
    | true =>
      simp only [d304047, d305715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304048 q = 1) (hb : d305716 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d304048, d305716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304048, d305716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304049 q = 1) (hb : d305717 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d304049, d305717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304049, d305717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304050 q = 1) (hb : d305718 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d304050, d305718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304050, d305718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304051 q = 1) (hb : d305719 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d304051, d305719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304051, d305719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304052 q = 1) (hb : d305720 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d304052, d305720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304052, d305720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78355 (p : Pattern) (ha : d304058 p = 1) (hb : d305726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304053 q = 1) (hb : d305721 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d304053, d305721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78354 q ha hb
    | true =>
      simp only [d304053, d305721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304054 q = 1) (hb : d305722 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d304054, d305722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304054, d305722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304055 q = 1) (hb : d305723 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d304055, d305723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304055, d305723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304056 q = 1) (hb : d305724 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d304056, d305724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304056, d305724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304057 q = 1) (hb : d305725 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d304057, d305725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304057, d305725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304058 q = 1) (hb : d305726 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d304058, d305726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304058, d305726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78356 (p : Pattern) (ha : d304064 p = 1) (hb : d305732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304059 q = 1) (hb : d305727 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d304059, d305727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78355 q ha hb
    | true =>
      simp only [d304059, d305727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304060 q = 1) (hb : d305728 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d304060, d305728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304060, d305728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304061 q = 1) (hb : d305729 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d304061, d305729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304061, d305729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304062 q = 1) (hb : d305730 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d304062, d305730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304062, d305730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304063 q = 1) (hb : d305731 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d304063, d305731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304063, d305731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304064 q = 1) (hb : d305732 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d304064, d305732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304064, d305732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78357 (p : Pattern) (ha : d304070 p = 1) (hb : d305738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304065 q = 1) (hb : d305733 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d304065, d305733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78356 q ha hb
    | true =>
      simp only [d304065, d305733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d304066 q = 1) (hb : d305734 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d304066, d305734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304066, d305734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d304067 q = 1) (hb : d305735 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d304067, d305735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304067, d305735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d304068 q = 1) (hb : d305736 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d304068, d305736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304068, d305736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d304069 q = 1) (hb : d305737 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d304069, d305737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304069, d305737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d304070 q = 1) (hb : d305738 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d304070, d305738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304070, d305738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro78358 (p : Pattern) (ha : d304159 p = 1) (hb : d305743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d300537 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304155 q = 1) (hb : d305739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304155, d305739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304155, d305739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d300428 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304156 q = 1) (hb : d305740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304156, d305740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304156, d305740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304157 q = 1) (hb : d305741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304157, d305741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304157, d305741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304158 q = 1) (hb : d305742 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304158, d305742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304158, d305742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304159 q = 1) (hb : d305743 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304159, d305743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304159, d305743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78359 (p : Pattern) (ha : d304166 p = 1) (hb : d305748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300511 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300537 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304155 q = 1) (hb : d305739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304155, d305739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304155, d305739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d300428 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304156 q = 1) (hb : d305740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304156, d305740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304156, d305740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304157 q = 1) (hb : d305741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304157, d305741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304157, d305741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304158 q = 1) (hb : d305742 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304158, d305742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304158, d305742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d300573 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d300577 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d300579 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304162 q = 1) (hb : d305744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304162, d305744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304162, d305744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d300435 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304163 q = 1) (hb : d305745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304163, d305745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304163, d305745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304164 q = 1) (hb : d305746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304164, d305746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304164, d305746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304165 q = 1) (hb : d305747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304165, d305747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304165, d305747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304166 q = 1) (hb : d305748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304166, d305748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304166, d305748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78360 (p : Pattern) (ha : d304381 p = 1) (hb : d305755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304162 q = 1) (hb : d305744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304162, d305744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304162, d305744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d300435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304163 q = 1) (hb : d305745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304163, d305745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304163, d305745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304164 q = 1) (hb : d305753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304164, d305753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304164, d305753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304165 q = 1) (hb : d305754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304165, d305754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304165, d305754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304381 q = 1) (hb : d305755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304381, d305755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304381, d305755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78361 (p : Pattern) (ha : d304427 p = 1) (hb : d305765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304423 q = 1) (hb : d305761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304423, d305761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304423, d305761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d300469 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304424 q = 1) (hb : d305762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304424, d305762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304424, d305762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304425 q = 1) (hb : d305763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304425, d305763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304425, d305763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304426 q = 1) (hb : d305764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304426, d305764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304426, d305764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304427 q = 1) (hb : d305765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304427, d305765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304427, d305765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78362 (p : Pattern) (ha : d305545 p = 1) (hb : d305771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304167 q = 1) (hb : d305749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304167, d305749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78358 q ha hb
    | true =>
      simp only [d304167, d305749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304168 q = 1) (hb : d305750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304168, d305750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304168, d305750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305535 q = 1) (hb : d305751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305535, d305751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305535, d305751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305536 q = 1) (hb : d305752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305536, d305752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305536, d305752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304382 q = 1) (hb : d305756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304382, d305756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304382, d305756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78360 q ha hb
  have h8 (q : Pattern) (ha : d305537 q = 1) (hb : d305757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305537, d305757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305537, d305757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d305538 q = 1) (hb : d305758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305538, d305758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d305538, d305758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d305539 q = 1) (hb : d305759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305539, d305759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305539, d305759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305540 q = 1) (hb : d305760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305540, d305760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305540, d305760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d304428 q = 1) (hb : d305766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304428, d305766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304428, d305766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78361 q ha hb
  have h13 (q : Pattern) (ha : d305541 q = 1) (hb : d305767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305541, d305767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305541, d305767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d305542 q = 1) (hb : d305768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305542, d305768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305542, d305768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d305543 q = 1) (hb : d305769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305543, d305769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d305543, d305769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d305544 q = 1) (hb : d305770 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305544, d305770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305544, d305770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305545 q = 1) (hb : d305771 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305545, d305771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d305545, d305771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro78363 (p : Pattern) (ha : d305551 p = 1) (hb : d305777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300484 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d305546 q = 1) (hb : d305772 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305546, d305772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305546, d305772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78362 q ha hb
  have h3 (q : Pattern) (ha : d305547 q = 1) (hb : d305773 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305547, d305773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305547, d305773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305548 q = 1) (hb : d305774 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305548, d305774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305548, d305774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305549 q = 1) (hb : d305775 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305549, d305775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305549, d305775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305550 q = 1) (hb : d305776 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305550, d305776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305550, d305776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305551 q = 1) (hb : d305777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305551, d305777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305551, d305777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro78364 (p : Pattern) (ha : d304284 p = 1) (hb : d305782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300676 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d300720 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304280 q = 1) (hb : d305778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d305778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304280, d305778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d300753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304281 q = 1) (hb : d305779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d305779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304281, d305779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304282 q = 1) (hb : d305780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d305780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304282, d305780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304283 q = 1) (hb : d305781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d305781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304283, d305781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304284 q = 1) (hb : d305782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304284, d305782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304284, d305782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78365 (p : Pattern) (ha : d304291 p = 1) (hb : d305787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300682 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304280 q = 1) (hb : d305778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d305778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304280, d305778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d300753 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304281 q = 1) (hb : d305779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d305779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304281, d305779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304282 q = 1) (hb : d305780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d305780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304282, d305780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304283 q = 1) (hb : d305781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d305781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304283, d305781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d300762 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d300766 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d300768 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304287 q = 1) (hb : d305783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d305783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304287, d305783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d300774 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304288 q = 1) (hb : d305784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d305784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304288, d305784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304289 q = 1) (hb : d305785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d305785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304289, d305785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304290 q = 1) (hb : d305786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d305786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304290, d305786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304291 q = 1) (hb : d305787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304291, d305787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304291, d305787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78366 (p : Pattern) (ha : d305554 p = 1) (hb : d305794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304287 q = 1) (hb : d305783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d305783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304287, d305783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d300774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304288 q = 1) (hb : d305784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d305784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304288, d305784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304289 q = 1) (hb : d305792 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d305792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304289, d305792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304290 q = 1) (hb : d305793 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d305793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304290, d305793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305554 q = 1) (hb : d305794 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305554, d305794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305554, d305794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78367 (p : Pattern) (ha : d305564 p = 1) (hb : d305804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305560 q = 1) (hb : d305800 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305560, d305800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305560, d305800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d300844 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305561 q = 1) (hb : d305801 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305561, d305801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305561, d305801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305562 q = 1) (hb : d305802 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305562, d305802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305562, d305802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305563 q = 1) (hb : d305803 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305563, d305803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305563, d305803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305564 q = 1) (hb : d305804 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305564, d305804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305564, d305804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78368 (p : Pattern) (ha : d305570 p = 1) (hb : d305810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300670 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304292 q = 1) (hb : d305788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304292, d305788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78364 q ha hb
    | true =>
      simp only [d304292, d305788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78365 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300781 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304293 q = 1) (hb : d305789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304293, d305789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304293, d305789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305552 q = 1) (hb : d305790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305552, d305790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305552, d305790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305553 q = 1) (hb : d305791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305553, d305791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305553, d305791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305555 q = 1) (hb : d305795 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305555, d305795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305555, d305795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78366 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d300790 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305556 q = 1) (hb : d305796 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305556, d305796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305556, d305796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305557 q = 1) (hb : d305797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305557, d305797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305557, d305797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305558 q = 1) (hb : d305798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305558, d305798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305558, d305798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305559 q = 1) (hb : d305799 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305559, d305799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305559, d305799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305565 q = 1) (hb : d305805 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305565, d305805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305565, d305805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78367 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d300855 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305566 q = 1) (hb : d305806 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305566, d305806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305566, d305806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305567 q = 1) (hb : d305807 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305567, d305807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305567, d305807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305568 q = 1) (hb : d305808 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305568, d305808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305568, d305808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305569 q = 1) (hb : d305809 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305569, d305809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305569, d305809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305570 q = 1) (hb : d305810 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305570, d305810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305570, d305810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78369 (p : Pattern) (ha : d305576 p = 1) (hb : d305816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305571 q = 1) (hb : d305811 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305571, d305811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305571, d305811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78368 q ha hb
  have h2 (q : Pattern) (ha : d305572 q = 1) (hb : d305812 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305572, d305812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305572, d305812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305573 q = 1) (hb : d305813 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305573, d305813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305573, d305813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305574 q = 1) (hb : d305814 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305574, d305814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305574, d305814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305575 q = 1) (hb : d305815 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305575, d305815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305575, d305815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305576 q = 1) (hb : d305816 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305576, d305816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305576, d305816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78370 (p : Pattern) (ha : d304463 p = 1) (hb : d305822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300920 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d300970 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304459 q = 1) (hb : d305818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d305818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304459, d305818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d301024 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304460 q = 1) (hb : d305819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d305819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304460, d305819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304461 q = 1) (hb : d305820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d305820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304461, d305820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304462 q = 1) (hb : d305821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d305821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304462, d305821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304463 q = 1) (hb : d305822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304463, d305822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304463, d305822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78371 (p : Pattern) (ha : d304473 p = 1) (hb : d305827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300911 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300920 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300970 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304459 q = 1) (hb : d305818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d305818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304459, d305818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d301024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304460 q = 1) (hb : d305819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d305819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304460, d305819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304461 q = 1) (hb : d305820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d305820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304461, d305820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304462 q = 1) (hb : d305821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d305821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304462, d305821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d301034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d301039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d301041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304469 q = 1) (hb : d305823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d305823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304469, d305823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d301048 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304470 q = 1) (hb : d305824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d305824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304470, d305824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304471 q = 1) (hb : d305825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d305825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304471, d305825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304472 q = 1) (hb : d305826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d305826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304472, d305826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304473 q = 1) (hb : d305827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304473, d305827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304473, d305827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78372 (p : Pattern) (ha : d305580 p = 1) (hb : d305834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304469 q = 1) (hb : d305823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d305823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304469, d305823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d301048 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304470 q = 1) (hb : d305824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d305824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304470, d305824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304471 q = 1) (hb : d305832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d305832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304471, d305832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304472 q = 1) (hb : d305833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d305833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304472, d305833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305580 q = 1) (hb : d305834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305580, d305834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305580, d305834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78373 (p : Pattern) (ha : d305591 p = 1) (hb : d305844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301124 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305586 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305587 q = 1) (hb : d305840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305587, d305840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305587, d305840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d301164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305588 q = 1) (hb : d305841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305588, d305841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305588, d305841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305589 q = 1) (hb : d305842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305589, d305842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305589, d305842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305590 q = 1) (hb : d305843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305590, d305843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305590, d305843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305591 q = 1) (hb : d305844 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305591, d305844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305591, d305844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78374 (p : Pattern) (ha : d305597 p = 1) (hb : d305850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300903 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304474 q = 1) (hb : d305828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304474, d305828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78370 q ha hb
    | true =>
      simp only [d304474, d305828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78371 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304475 q = 1) (hb : d305829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304475, d305829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304475, d305829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305578 q = 1) (hb : d305830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305578, d305830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305578, d305830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305579 q = 1) (hb : d305831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305579, d305831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305579, d305831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305581 q = 1) (hb : d305835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305581, d305835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305581, d305835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78372 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d301075 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305582 q = 1) (hb : d305836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305582, d305836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305582, d305836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305583 q = 1) (hb : d305837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305583, d305837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305583, d305837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305584 q = 1) (hb : d305838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305584, d305838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305584, d305838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305585 q = 1) (hb : d305839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305585, d305839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305585, d305839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305592 q = 1) (hb : d305845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305592, d305845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305592, d305845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78373 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d301180 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305593 q = 1) (hb : d305846 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305593, d305846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305593, d305846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305594 q = 1) (hb : d305847 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305594, d305847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305594, d305847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305595 q = 1) (hb : d305848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305595, d305848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305595, d305848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305596 q = 1) (hb : d305849 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305596, d305849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305596, d305849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305597 q = 1) (hb : d305850 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305597, d305850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305597, d305850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78375 (p : Pattern) (ha : d305603 p = 1) (hb : d305856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305598 q = 1) (hb : d305851 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305598, d305851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305598, d305851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78374 q ha hb
  have h2 (q : Pattern) (ha : d305599 q = 1) (hb : d305852 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305599, d305852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305599, d305852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305600 q = 1) (hb : d305853 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305600, d305853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305600, d305853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305601 q = 1) (hb : d305854 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305601, d305854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305601, d305854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305602 q = 1) (hb : d305855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305602, d305855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305602, d305855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305603 q = 1) (hb : d305856 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305603, d305856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305603, d305856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78376 (p : Pattern) (ha : d304722 p = 1) (hb : d305863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d301304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304717 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304718 q = 1) (hb : d305859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304718, d305859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304718, d305859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d301378 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304719 q = 1) (hb : d305860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304719, d305860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304719, d305860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304720 q = 1) (hb : d305861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304720, d305861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304720, d305861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304721 q = 1) (hb : d305862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304721, d305862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304721, d305862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304722 q = 1) (hb : d305863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304722, d305863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304722, d305863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78377 (p : Pattern) (ha : d304732 p = 1) (hb : d305868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d301255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304717 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304718 q = 1) (hb : d305859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304718, d305859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304718, d305859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d301378 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304719 q = 1) (hb : d305860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304719, d305860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304719, d305860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304720 q = 1) (hb : d305861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304720, d305861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304720, d305861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304721 q = 1) (hb : d305862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304721, d305862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304721, d305862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d301388 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d301393 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d301395 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304727 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304728 q = 1) (hb : d305864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304728, d305864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304728, d305864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d301402 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304729 q = 1) (hb : d305865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304729, d305865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304729, d305865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304730 q = 1) (hb : d305866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304730, d305866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304730, d305866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304731 q = 1) (hb : d305867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304731, d305867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304731, d305867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304732 q = 1) (hb : d305868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304732, d305868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304732, d305868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78378 (p : Pattern) (ha : d305608 p = 1) (hb : d305875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304728 q = 1) (hb : d305864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304728, d305864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304728, d305864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d301402 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304729 q = 1) (hb : d305865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304729, d305865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304729, d305865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304730 q = 1) (hb : d305873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304730, d305873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304730, d305873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304731 q = 1) (hb : d305874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304731, d305874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304731, d305874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305608 q = 1) (hb : d305875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305608, d305875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305608, d305875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78379 (p : Pattern) (ha : d305619 p = 1) (hb : d305885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305615 q = 1) (hb : d305881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305615, d305881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305615, d305881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d301550 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305616 q = 1) (hb : d305882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305616, d305882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305616, d305882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305617 q = 1) (hb : d305883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305617, d305883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305617, d305883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305618 q = 1) (hb : d305884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305618, d305884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305618, d305884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305619 q = 1) (hb : d305885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305619, d305885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305619, d305885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78380 (p : Pattern) (ha : d305625 p = 1) (hb : d305891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d301247 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304733 q = 1) (hb : d305869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304733, d305869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78376 q ha hb
    | true =>
      simp only [d304733, d305869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78377 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301420 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304734 q = 1) (hb : d305870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304734, d305870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304734, d305870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305606 q = 1) (hb : d305871 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305606, d305871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305606, d305871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305607 q = 1) (hb : d305872 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305607, d305872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305607, d305872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305609 q = 1) (hb : d305876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305609, d305876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305609, d305876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78378 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d301429 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305610 q = 1) (hb : d305877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305610, d305877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305610, d305877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305611 q = 1) (hb : d305878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305611, d305878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305611, d305878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305612 q = 1) (hb : d305879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305612, d305879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305612, d305879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305613 q = 1) (hb : d305880 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305613, d305880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305613, d305880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305620 q = 1) (hb : d305886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305620, d305886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305620, d305886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78379 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d301566 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305621 q = 1) (hb : d305887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305621, d305887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305621, d305887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305622 q = 1) (hb : d305888 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305622, d305888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305622, d305888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305623 q = 1) (hb : d305889 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305623, d305889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305623, d305889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305624 q = 1) (hb : d305890 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305624, d305890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305624, d305890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305625 q = 1) (hb : d305891 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305625, d305891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305625, d305891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78381 (p : Pattern) (ha : d305631 p = 1) (hb : d305897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305626 q = 1) (hb : d305892 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305626, d305892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305626, d305892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78380 q ha hb
  have h2 (q : Pattern) (ha : d305627 q = 1) (hb : d305893 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305627, d305893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305627, d305893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305628 q = 1) (hb : d305894 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305628, d305894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305628, d305894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305629 q = 1) (hb : d305895 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305629, d305895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305629, d305895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305630 q = 1) (hb : d305896 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305630, d305896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305630, d305896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305631 q = 1) (hb : d305897 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305631, d305897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305631, d305897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78382 (p : Pattern) (ha : d305012 p = 1) (hb : d305905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301687 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d301712 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d305007 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305008 q = 1) (hb : d305901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305008, d305901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305008, d305901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d301817 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d305009 q = 1) (hb : d305902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305009, d305902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305009, d305902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305010 q = 1) (hb : d305903 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305010, d305903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305010, d305903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d305011 q = 1) (hb : d305904 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305011, d305904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305011, d305904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305012 q = 1) (hb : d305905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305012, d305905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305012, d305905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78383 (p : Pattern) (ha : d305022 p = 1) (hb : d305910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d301678 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301712 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d305007 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d305008 q = 1) (hb : d305901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305008, d305901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305008, d305901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d301817 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d305009 q = 1) (hb : d305902 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305009, d305902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305009, d305902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305010 q = 1) (hb : d305903 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305010, d305903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305010, d305903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305011 q = 1) (hb : d305904 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305011, d305904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305011, d305904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d301827 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d301832 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d301834 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d305017 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d305018 q = 1) (hb : d305906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305018, d305906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d305018, d305906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d301841 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305019 q = 1) (hb : d305907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305019, d305907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305019, d305907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305020 q = 1) (hb : d305908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305020, d305908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305020, d305908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d305021 q = 1) (hb : d305909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305021, d305909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305021, d305909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d305022 q = 1) (hb : d305910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305022, d305910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d305022, d305910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78384 (p : Pattern) (ha : d305637 p = 1) (hb : d305917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305018 q = 1) (hb : d305906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305018, d305906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305018, d305906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d301841 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305019 q = 1) (hb : d305907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305019, d305907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305019, d305907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305020 q = 1) (hb : d305915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305020, d305915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305020, d305915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305021 q = 1) (hb : d305916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305021, d305916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305021, d305916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305637 q = 1) (hb : d305917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305637, d305917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305637, d305917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78385 (p : Pattern) (ha : d305648 p = 1) (hb : d305927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d301944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305644 q = 1) (hb : d305923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305644, d305923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305644, d305923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302023 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305645 q = 1) (hb : d305924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305645, d305924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305645, d305924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305646 q = 1) (hb : d305925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305646, d305925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305646, d305925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305647 q = 1) (hb : d305926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305647, d305926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305647, d305926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305648 q = 1) (hb : d305927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305648, d305927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305648, d305927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78386 (p : Pattern) (ha : d305654 p = 1) (hb : d305933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d301670 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305023 q = 1) (hb : d305911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305023, d305911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78382 q ha hb
    | true =>
      simp only [d305023, d305911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78383 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d301859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305024 q = 1) (hb : d305912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305024, d305912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305024, d305912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305635 q = 1) (hb : d305913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305635, d305913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305635, d305913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305636 q = 1) (hb : d305914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305636, d305914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305636, d305914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305638 q = 1) (hb : d305918 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305638, d305918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305638, d305918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78384 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d301868 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305639 q = 1) (hb : d305919 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305639, d305919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305639, d305919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305640 q = 1) (hb : d305920 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305640, d305920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305640, d305920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305641 q = 1) (hb : d305921 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305641, d305921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305641, d305921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305642 q = 1) (hb : d305922 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305642, d305922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305642, d305922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305649 q = 1) (hb : d305928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305649, d305928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305649, d305928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78385 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d302039 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305650 q = 1) (hb : d305929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305650, d305929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305650, d305929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305651 q = 1) (hb : d305930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305651, d305930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305651, d305930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305652 q = 1) (hb : d305931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305652, d305931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305652, d305931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305653 q = 1) (hb : d305932 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305653, d305932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305653, d305932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305654 q = 1) (hb : d305933 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305654, d305933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305654, d305933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78387 (p : Pattern) (ha : d305660 p = 1) (hb : d305939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305655 q = 1) (hb : d305934 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305655, d305934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305655, d305934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78386 q ha hb
  have h2 (q : Pattern) (ha : d305656 q = 1) (hb : d305935 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305656, d305935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305656, d305935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305657 q = 1) (hb : d305936 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305657, d305936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305657, d305936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305658 q = 1) (hb : d305937 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305658, d305937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305658, d305937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305659 q = 1) (hb : d305938 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305659, d305938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305659, d305938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305660 q = 1) (hb : d305939 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305660, d305939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305660, d305939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78388 (p : Pattern) (ha : d305283 p = 1) (hb : d305948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d302168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d305278 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305279 q = 1) (hb : d305944 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305279, d305944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305279, d305944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d302259 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d305280 q = 1) (hb : d305945 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305280, d305945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305280, d305945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305281 q = 1) (hb : d305946 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305281, d305946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305281, d305946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d305282 q = 1) (hb : d305947 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305282, d305947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305282, d305947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305283 q = 1) (hb : d305948 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305283, d305948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305283, d305948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78389 (p : Pattern) (ha : d305293 p = 1) (hb : d305953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d305278 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d305279 q = 1) (hb : d305944 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305279, d305944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305279, d305944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d302259 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d305280 q = 1) (hb : d305945 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305280, d305945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305280, d305945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305281 q = 1) (hb : d305946 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305281, d305946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305281, d305946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305282 q = 1) (hb : d305947 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305282, d305947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305282, d305947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d302269 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d302274 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d302276 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d305288 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d305289 q = 1) (hb : d305949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305289, d305949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d305289, d305949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d302283 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305290 q = 1) (hb : d305950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305290, d305950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305290, d305950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305291 q = 1) (hb : d305951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305291, d305951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305291, d305951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d305292 q = 1) (hb : d305952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305292, d305952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305292, d305952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d305293 q = 1) (hb : d305953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305293, d305953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d305293, d305953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78390 (p : Pattern) (ha : d305667 p = 1) (hb : d305960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305288 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305289 q = 1) (hb : d305949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305289, d305949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305289, d305949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302283 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305290 q = 1) (hb : d305950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305290, d305950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305290, d305950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305291 q = 1) (hb : d305958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305291, d305958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305291, d305958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305292 q = 1) (hb : d305959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305292, d305959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305292, d305959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305667 q = 1) (hb : d305960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305667, d305960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305667, d305960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78391 (p : Pattern) (ha : d305678 p = 1) (hb : d305970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d302367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305673 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305674 q = 1) (hb : d305966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305674, d305966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305674, d305966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d302433 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305675 q = 1) (hb : d305967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305675, d305967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305675, d305967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305676 q = 1) (hb : d305968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305676, d305968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305676, d305968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305677 q = 1) (hb : d305969 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305677, d305969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305677, d305969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305678 q = 1) (hb : d305970 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305678, d305970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305678, d305970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78392 (p : Pattern) (ha : d305684 p = 1) (hb : d305976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d302137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305294 q = 1) (hb : d305954 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305294, d305954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78388 q ha hb
    | true =>
      simp only [d305294, d305954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78389 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d302301 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305295 q = 1) (hb : d305955 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305295, d305955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305295, d305955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305665 q = 1) (hb : d305956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305665, d305956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305665, d305956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305666 q = 1) (hb : d305957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305666, d305957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305666, d305957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305668 q = 1) (hb : d305961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305668, d305961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305668, d305961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78390 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d302310 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305669 q = 1) (hb : d305962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305669, d305962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305669, d305962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305670 q = 1) (hb : d305963 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305670, d305963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305670, d305963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305671 q = 1) (hb : d305964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305671, d305964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305671, d305964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305672 q = 1) (hb : d305965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305672, d305965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305672, d305965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305679 q = 1) (hb : d305971 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305679, d305971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305679, d305971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78391 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d302449 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305680 q = 1) (hb : d305972 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305680, d305972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305680, d305972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305681 q = 1) (hb : d305973 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305681, d305973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305681, d305973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305682 q = 1) (hb : d305974 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305682, d305974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305682, d305974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305683 q = 1) (hb : d305975 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305683, d305975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305683, d305975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305684 q = 1) (hb : d305976 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305684, d305976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305684, d305976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78393 (p : Pattern) (ha : d305690 p = 1) (hb : d305982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305685 q = 1) (hb : d305977 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305685, d305977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305685, d305977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78392 q ha hb
  have h2 (q : Pattern) (ha : d305686 q = 1) (hb : d305978 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305686, d305978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305686, d305978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305687 q = 1) (hb : d305979 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305687, d305979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305687, d305979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305688 q = 1) (hb : d305980 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305688, d305980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305688, d305980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305689 q = 1) (hb : d305981 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305689, d305981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305689, d305981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305690 q = 1) (hb : d305982 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305690, d305982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305690, d305982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78394 (p : Pattern) (ha : d305696 p = 1) (hb : d305988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d305577 q = 1) (hb : d305817 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305577, d305817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78363 q ha hb
    | true =>
      simp only [d305577, d305817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78369 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d305604 q = 1) (hb : d305857 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305604, d305857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305604, d305857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78375 q ha hb
  have h3 (q : Pattern) (ha : d305605 q = 1) (hb : d305858 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305605, d305858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305605, d305858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305632 q = 1) (hb : d305898 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305632, d305898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305632, d305898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78381 q ha hb
  have h5 (q : Pattern) (ha : d305633 q = 1) (hb : d305899 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305633, d305899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305633, d305899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305634 q = 1) (hb : d305900 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d305634, d305900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305634, d305900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305661 q = 1) (hb : d305940 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305661, d305940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305661, d305940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78387 q ha hb
  have h8 (q : Pattern) (ha : d305662 q = 1) (hb : d305941 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305662, d305941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305662, d305941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d305663 q = 1) (hb : d305942 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d305663, d305942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305663, d305942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305664 q = 1) (hb : d305943 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d305664, d305943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305664, d305943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d305691 q = 1) (hb : d305983 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305691, d305983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305691, d305983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78393 q ha hb
  have h12 (q : Pattern) (ha : d305692 q = 1) (hb : d305984 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305692, d305984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305692, d305984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305693 q = 1) (hb : d305985 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d305693, d305985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305693, d305985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d305694 q = 1) (hb : d305986 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d305694, d305986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305694, d305986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d305695 q = 1) (hb : d305987 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d305695, d305987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305695, d305987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305696 q = 1) (hb : d305988 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d305696, d305988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305696, d305988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro78395 (p : Pattern) (ha : d305702 p = 1) (hb : d305994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305697 q = 1) (hb : d305989 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d305697, d305989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78394 q ha hb
    | true =>
      simp only [d305697, d305989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305698 q = 1) (hb : d305990 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d305698, d305990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305698, d305990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305699 q = 1) (hb : d305991 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d305699, d305991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305699, d305991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305700 q = 1) (hb : d305992 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d305700, d305992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305700, d305992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305701 q = 1) (hb : d305993 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d305701, d305993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305701, d305993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305702 q = 1) (hb : d305994 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d305702, d305994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305702, d305994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78396 (p : Pattern) (ha : d305708 p = 1) (hb : d306000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305703 q = 1) (hb : d305995 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d305703, d305995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78395 q ha hb
    | true =>
      simp only [d305703, d305995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305704 q = 1) (hb : d305996 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d305704, d305996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305704, d305996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305705 q = 1) (hb : d305997 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d305705, d305997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305705, d305997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305706 q = 1) (hb : d305998 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d305706, d305998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305706, d305998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305707 q = 1) (hb : d305999 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d305707, d305999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305707, d305999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305708 q = 1) (hb : d306000 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d305708, d306000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305708, d306000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78397 (p : Pattern) (ha : d305714 p = 1) (hb : d306006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305709 q = 1) (hb : d306001 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d305709, d306001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78396 q ha hb
    | true =>
      simp only [d305709, d306001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305710 q = 1) (hb : d306002 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d305710, d306002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305710, d306002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305711 q = 1) (hb : d306003 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d305711, d306003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305711, d306003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305712 q = 1) (hb : d306004 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d305712, d306004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305712, d306004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305713 q = 1) (hb : d306005 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d305713, d306005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305713, d306005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305714 q = 1) (hb : d306006 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d305714, d306006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305714, d306006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78398 (p : Pattern) (ha : d305720 p = 1) (hb : d306012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305715 q = 1) (hb : d306007 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d305715, d306007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78397 q ha hb
    | true =>
      simp only [d305715, d306007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305716 q = 1) (hb : d306008 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d305716, d306008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305716, d306008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305717 q = 1) (hb : d306009 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d305717, d306009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305717, d306009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305718 q = 1) (hb : d306010 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d305718, d306010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305718, d306010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305719 q = 1) (hb : d306011 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d305719, d306011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305719, d306011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305720 q = 1) (hb : d306012 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d305720, d306012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305720, d306012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78399 (p : Pattern) (ha : d305726 p = 1) (hb : d306018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305721 q = 1) (hb : d306013 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d305721, d306013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78398 q ha hb
    | true =>
      simp only [d305721, d306013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305722 q = 1) (hb : d306014 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d305722, d306014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305722, d306014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305723 q = 1) (hb : d306015 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d305723, d306015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305723, d306015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305724 q = 1) (hb : d306016 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d305724, d306016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305724, d306016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305725 q = 1) (hb : d306017 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d305725, d306017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305725, d306017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305726 q = 1) (hb : d306018 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d305726, d306018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305726, d306018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78400 (p : Pattern) (ha : d305732 p = 1) (hb : d306024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305727 q = 1) (hb : d306019 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d305727, d306019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78399 q ha hb
    | true =>
      simp only [d305727, d306019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305728 q = 1) (hb : d306020 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d305728, d306020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305728, d306020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305729 q = 1) (hb : d306021 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d305729, d306021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305729, d306021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305730 q = 1) (hb : d306022 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d305730, d306022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305730, d306022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305731 q = 1) (hb : d306023 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d305731, d306023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305731, d306023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305732 q = 1) (hb : d306024 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d305732, d306024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305732, d306024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78401 (p : Pattern) (ha : d305738 p = 1) (hb : d306030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305733 q = 1) (hb : d306025 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d305733, d306025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78400 q ha hb
    | true =>
      simp only [d305733, d306025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d305734 q = 1) (hb : d306026 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d305734, d306026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305734, d306026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305735 q = 1) (hb : d306027 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d305735, d306027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305735, d306027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d305736 q = 1) (hb : d306028 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d305736, d306028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305736, d306028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305737 q = 1) (hb : d306029 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d305737, d306029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305737, d306029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d305738 q = 1) (hb : d306030 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d305738, d306030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305738, d306030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78402 (p : Pattern) (ha : d31626 p = 1) (hb : d241830 p = 1) : d31312 p = 1 := by
  have h0 (q : Pattern) (ha : d31308 q = 1) (hb : d241830 q = 1) : d31308 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30968 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31623 q = 1) (hb : d241830 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31309 q = 1) (hb : d241830 q = 1) : d31309 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d31624 q = 1) (hb : d241830 q = 1) : d31310 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31624, d31310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31624, d31310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31625 q = 1) (hb : d241830 q = 1) : d31311 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31625, d31311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31625, d31311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d31626 q = 1) (hb : d241830 q = 1) : d31312 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31626, d31312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31626, d31312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78403 (p : Pattern) (ha : d31636 p = 1) (hb : d241830 p = 1) : d31317 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241830 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30973 q = 1) (hb : d241830 q = 1) : d30973 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31631 q = 1) (hb : d241830 q = 1) : d30974 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31632 q = 1) (hb : d241830 q = 1) : d30975 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d25434 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31633 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31634 q = 1) (hb : d241830 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h13 (q : Pattern) (ha : d31635 q = 1) (hb : d241830 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d31636 q = 1) (hb : d241830 q = 1) : d31317 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31636, d31317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31636, d31317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro78404 (p : Pattern) (ha : d31642 p = 1) (hb : d241830 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d31324 q = 1) (hb : d241830 q = 1) : d31324 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25434 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31633 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31634 q = 1) (hb : d241830 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d31635 q = 1) (hb : d241830 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d31642 q = 1) (hb : d241830 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31642, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31642, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78405 (p : Pattern) (ha : d31649 p = 1) (hb : d241830 p = 1) : d281108 p = 1 := by
  have h0 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25434 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31633 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25435 q = 1) (hb : d241830 q = 1) : d25435 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31647 q = 1) (hb : d241830 q = 1) : d281106 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31647, d281106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31647, d281106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31648 q = 1) (hb : d241830 q = 1) : d281107 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31648, d281107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31648, d281107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1116 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d241830 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1117 q = 1) (hb : d241830 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21 q = 1) (hb : d241830 q = 1) : d21 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1118 q = 1) (hb : d241830 q = 1) : d29091 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1119 q = 1) (hb : d241830 q = 1) : d29092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d31649 q = 1) (hb : d241830 q = 1) : d281108 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31649, d281108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31649, d281108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78406 (p : Pattern) (ha : d31655 p = 1) (hb : d241830 p = 1) : d281114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31627 q = 1) (hb : d241830 q = 1) : d31313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78402 q ha hb
    | true =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31628 q = 1) (hb : d241830 q = 1) : d31314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31629 q = 1) (hb : d241830 q = 1) : d31315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31629, d31315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31629, d31315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31630 q = 1) (hb : d241830 q = 1) : d31316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31630, d31316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31630, d31316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31637 q = 1) (hb : d241830 q = 1) : d31318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78403 q ha hb
    | true =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31638 q = 1) (hb : d241830 q = 1) : d31319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31639 q = 1) (hb : d241830 q = 1) : d31320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31639, d31320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31639, d31320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31640 q = 1) (hb : d241830 q = 1) : d31321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31640, d31321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31640, d31321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31641 q = 1) (hb : d241830 q = 1) : d31322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31641, d31322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31641, d31322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31643 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31644 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31645 q = 1) (hb : d241830 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31646 q = 1) (hb : d241830 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31652 q = 1) (hb : d241830 q = 1) : d281111 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31653 q = 1) (hb : d241830 q = 1) : d281112 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31654 q = 1) (hb : d241830 q = 1) : d281113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31654, d281113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31654, d281113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31655 q = 1) (hb : d241830 q = 1) : d281114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31655, d281114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31655, d281114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78407 (p : Pattern) (ha : d31661 p = 1) (hb : d241830 p = 1) : d30976 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241830 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30973 q = 1) (hb : d241830 q = 1) : d30973 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31631 q = 1) (hb : d241830 q = 1) : d30974 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31632 q = 1) (hb : d241830 q = 1) : d30975 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d25432 q = 1) (hb : d202304 q = 1) : d25432 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d31656 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d31657 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d31658 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31658, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30635 q = 1) (hb : d241830 q = 1) : d30635 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d31659 q = 1) (hb : d241830 q = 1) : d30748 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31659, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31660 q = 1) (hb : d241830 q = 1) : d30749 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31660, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d31661 q = 1) (hb : d241830 q = 1) : d30976 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31661, d30976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31661, d30976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro78408 (p : Pattern) (ha : d31666 p = 1) (hb : d241830 p = 1) : d281115 p = 1 := by
  have h0 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25432 q = 1) (hb : d202304 q = 1) : d25432 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31656 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d31657 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d31658 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31658, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30635 q = 1) (hb : d241830 q = 1) : d30635 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31659 q = 1) (hb : d241830 q = 1) : d30748 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31659, d30748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31660 q = 1) (hb : d241830 q = 1) : d30749 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31660, d30749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h15 (q : Pattern) (ha : d1116 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d241830 q = 1) : d20 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1117 q = 1) (hb : d241830 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21 q = 1) (hb : d241830 q = 1) : d21 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1118 q = 1) (hb : d241830 q = 1) : d29091 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1119 q = 1) (hb : d241830 q = 1) : d29092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h21 (q : Pattern) (ha : d31666 q = 1) (hb : d241830 q = 1) : d281115 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31666, d281115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31666, d281115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro78409 (p : Pattern) (ha : d31673 p = 1) (hb : d241830 p = 1) : d281122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31662 q = 1) (hb : d241830 q = 1) : d30977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d30977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78407 q ha hb
    | true =>
      simp only [d31662, d30977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31663 q = 1) (hb : d241830 q = 1) : d30978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d30978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31663, d30978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31664 q = 1) (hb : d241830 q = 1) : d30979 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31664, d30979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31664, d30979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31665 q = 1) (hb : d241830 q = 1) : d30980 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31665, d30980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31665, d30980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31669 q = 1) (hb : d241830 q = 1) : d281118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31670 q = 1) (hb : d241830 q = 1) : d281119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31671 q = 1) (hb : d241830 q = 1) : d281120 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31671, d281120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31671, d281120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31652 q = 1) (hb : d241830 q = 1) : d281111 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31653 q = 1) (hb : d241830 q = 1) : d281112 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31672 q = 1) (hb : d241830 q = 1) : d281121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d281121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31672, d281121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31673 q = 1) (hb : d241830 q = 1) : d281122 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31673, d281122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31673, d281122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78410 (p : Pattern) (ha : d9843 p = 1) (hb : d241830 p = 1) : d29114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1116 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1132 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d241830 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9841 q = 1) (hb : d241830 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9841, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9842 q = 1) (hb : d241830 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9842, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d9843 q = 1) (hb : d241830 q = 1) : d29114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9843, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h9 p ha hb
theorem andIntro78411 (p : Pattern) (ha : d31678 p = 1) (hb : d241830 p = 1) : d281127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d241830 q = 1) : d281118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d241830 q = 1) : d281119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d241830 q = 1) : d281126 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d281126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d281126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d241830 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78410 q ha hb
    | true =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d241830 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d241830 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d241830 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d241830 q = 1) : d29119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31678 q = 1) (hb : d241830 q = 1) : d281127 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31678, d281127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31678, d281127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78412 (p : Pattern) (ha : d31685 p = 1) (hb : d241830 p = 1) : d281134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d241830 q = 1) : d281123 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78406 q ha hb
    | true =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d241830 q = 1) : d281124 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d241830 q = 1) : d281125 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d241830 q = 1) : d281128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
    | true =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78411 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d241830 q = 1) : d281129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d241830 q = 1) : d281130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d241830 q = 1) : d281131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31683 q = 1) (hb : d241830 q = 1) : d281132 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d281132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31683, d281132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31684 q = 1) (hb : d241830 q = 1) : d281133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31684, d281133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31684, d281133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31685 q = 1) (hb : d241830 q = 1) : d281134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31685, d281134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31685, d281134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro78413 (p : Pattern) (ha : d31689 p = 1) (hb : d241830 p = 1) : d281138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31679 q = 1) (hb : d241830 q = 1) : d281128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
    | true =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78411 q ha hb
  have h2 (q : Pattern) (ha : d31680 q = 1) (hb : d241830 q = 1) : d281129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31681 q = 1) (hb : d241830 q = 1) : d281130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31683 q = 1) (hb : d241830 q = 1) : d281132 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d281132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31683, d281132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31688 q = 1) (hb : d241830 q = 1) : d281137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31688, d281137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31688, d281137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31689 q = 1) (hb : d241830 q = 1) : d281138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31689, d281138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31689, d281138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78414 (p : Pattern) (ha : d31695 p = 1) (hb : d241830 p = 1) : d281144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241830 q = 1) : d281142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d241830 q = 1) : d281143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d281143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d281143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31695 q = 1) (hb : d241830 q = 1) : d281144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31695, d281144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31695, d281144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78415 (p : Pattern) (ha : d31699 p = 1) (hb : d241830 p = 1) : d281148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241830 q = 1) : d281146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d241830 q = 1) : d281147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d281147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d281147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31699 q = 1) (hb : d241830 q = 1) : d281148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31699, d281148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31699, d281148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78416 (p : Pattern) (ha : d31705 p = 1) (hb : d241830 p = 1) : d281154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241830 q = 1) : d281149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78414 q ha hb
    | true =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78415 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241830 q = 1) : d281150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241830 q = 1) : d281151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241830 q = 1) : d281152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241830 q = 1) : d281153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31705 q = 1) (hb : d241830 q = 1) : d281154 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31705, d281154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31705, d281154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78417 (p : Pattern) (ha : d31708 p = 1) (hb : d241830 p = 1) : d281157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241830 q = 1) : d281142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d241830 q = 1) : d281143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d281143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d281143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31708 q = 1) (hb : d241830 q = 1) : d281157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31708, d281157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31708, d281157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78418 (p : Pattern) (ha : d31709 p = 1) (hb : d241830 p = 1) : d281158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241830 q = 1) : d281146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d241830 q = 1) : d281147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d281147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d281147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31709 q = 1) (hb : d241830 q = 1) : d281158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31709, d281158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31709, d281158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78419 (p : Pattern) (ha : d31715 p = 1) (hb : d241830 p = 1) : d281164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241830 q = 1) : d281149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78414 q ha hb
    | true =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78415 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241830 q = 1) : d281150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241830 q = 1) : d281151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241830 q = 1) : d281152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241830 q = 1) : d281153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31710 q = 1) (hb : d241830 q = 1) : d281159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d281159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78417 q ha hb
    | true =>
      simp only [d31710, d281159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78418 q ha hb
  have h7 (q : Pattern) (ha : d31711 q = 1) (hb : d241830 q = 1) : d281160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31712 q = 1) (hb : d241830 q = 1) : d281161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31712, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31713 q = 1) (hb : d241830 q = 1) : d281162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31714 q = 1) (hb : d241830 q = 1) : d281163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31715 q = 1) (hb : d241830 q = 1) : d281164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31715, d281164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31715, d281164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78420 (p : Pattern) (ha : d31927 p = 1) (hb : d241830 p = 1) : d281250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241830 q = 1) : d281149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78414 q ha hb
    | true =>
      simp only [d31700, d281149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78415 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241830 q = 1) : d281150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d281150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241830 q = 1) : d281151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d281151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241830 q = 1) : d281152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d281152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241830 q = 1) : d281153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d281153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31922 q = 1) (hb : d241830 q = 1) : d281245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d281245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78415 q ha hb
    | true =>
      simp only [d31922, d281245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31923 q = 1) (hb : d241830 q = 1) : d281246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d281246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d281246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31924 q = 1) (hb : d241830 q = 1) : d281247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d281247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31924, d281247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31925 q = 1) (hb : d241830 q = 1) : d281248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d281248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d281248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31926 q = 1) (hb : d241830 q = 1) : d281249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d281249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d281249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31927 q = 1) (hb : d241830 q = 1) : d281250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31927, d281250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31927, d281250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78421 (p : Pattern) (ha : d31933 p = 1) (hb : d241830 p = 1) : d281256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31922 q = 1) (hb : d241830 q = 1) : d281245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d281245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78415 q ha hb
    | true =>
      simp only [d31922, d281245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31923 q = 1) (hb : d241830 q = 1) : d281246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d281246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d281246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31924 q = 1) (hb : d241830 q = 1) : d281247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d281247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31924, d281247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31925 q = 1) (hb : d241830 q = 1) : d281248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d281248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d281248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31926 q = 1) (hb : d241830 q = 1) : d281249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d281249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d281249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31928 q = 1) (hb : d241830 q = 1) : d281251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d281251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78418 q ha hb
    | true =>
      simp only [d31928, d281251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31929 q = 1) (hb : d241830 q = 1) : d281252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d281252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d281252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31930 q = 1) (hb : d241830 q = 1) : d281253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d281253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31930, d281253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31931 q = 1) (hb : d241830 q = 1) : d281254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d281254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d281254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31932 q = 1) (hb : d241830 q = 1) : d281255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d281255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d281255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31933 q = 1) (hb : d241830 q = 1) : d281256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31933, d281256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31933, d281256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78422 (p : Pattern) (ha : d31942 p = 1) (hb : d241830 p = 1) : d281265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31928 q = 1) (hb : d241830 q = 1) : d281251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d281251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78418 q ha hb
    | true =>
      simp only [d31928, d281251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31929 q = 1) (hb : d241830 q = 1) : d281252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d281252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d281252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31930 q = 1) (hb : d241830 q = 1) : d281253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d281253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31930, d281253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31931 q = 1) (hb : d241830 q = 1) : d281254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d281254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d281254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31932 q = 1) (hb : d241830 q = 1) : d281255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d281255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d281255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31942 q = 1) (hb : d241830 q = 1) : d281265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31942, d281265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31942, d281265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78423 (p : Pattern) (ha : d32005 p = 1) (hb : d241830 p = 1) : d281292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31996 q = 1) (hb : d241830 q = 1) : d31118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31996, d31118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31996, d31118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78407 q ha hb
  have h2 (q : Pattern) (ha : d31662 q = 1) (hb : d241830 q = 1) : d30977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d30977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78407 q ha hb
    | true =>
      simp only [d31662, d30977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31997 q = 1) (hb : d241830 q = 1) : d31119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31997, d31119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31997, d31119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31663 q = 1) (hb : d241830 q = 1) : d30978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d30978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31663, d30978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31998 q = 1) (hb : d241830 q = 1) : d31120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31998, d31120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31998, d31120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31999 q = 1) (hb : d241830 q = 1) : d31121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31999, d31121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31999, d31121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32000 q = 1) (hb : d241830 q = 1) : d281287 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
  have h8 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32001 q = 1) (hb : d241830 q = 1) : d281288 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32002 q = 1) (hb : d241830 q = 1) : d281289 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32003 q = 1) (hb : d241830 q = 1) : d281290 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32004 q = 1) (hb : d241830 q = 1) : d281291 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32004, d281291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32004, d281291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31976 q = 1) (hb : d241830 q = 1) : d281272 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
  have h15 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31977 q = 1) (hb : d241830 q = 1) : d281273 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31978 q = 1) (hb : d241830 q = 1) : d281274 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31979 q = 1) (hb : d241830 q = 1) : d281275 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31990 q = 1) (hb : d241830 q = 1) : d281281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d281281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31990, d281281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32005 q = 1) (hb : d241830 q = 1) : d281292 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32005, d281292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32005, d281292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro78424 (p : Pattern) (ha : d32010 p = 1) (hb : d241830 p = 1) : d281297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d241830 q = 1) : d281287 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d241830 q = 1) : d281288 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d241830 q = 1) : d281289 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d241830 q = 1) : d281290 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d241830 q = 1) : d281296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d281296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d281296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d241830 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78410 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d241830 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78410 q ha hb
    | true =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d241830 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d241830 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d241830 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d241830 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d241830 q = 1) : d29399 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32010 q = 1) (hb : d241830 q = 1) : d281297 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32010, d281297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32010, d281297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78425 (p : Pattern) (ha : d32029 p = 1) (hb : d241830 p = 1) : d281316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32011 q = 1) (hb : d241830 q = 1) : d281298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
    | true =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78424 q ha hb
  have h2 (q : Pattern) (ha : d32012 q = 1) (hb : d241830 q = 1) : d281299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32013 q = 1) (hb : d241830 q = 1) : d281300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32019 q = 1) (hb : d241830 q = 1) : d281306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d281306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32019, d281306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32028 q = 1) (hb : d241830 q = 1) : d281315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32028, d281315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32028, d281315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32029 q = 1) (hb : d241830 q = 1) : d281316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32029, d281316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32029, d281316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78426 (p : Pattern) (ha : d32118 p = 1) (hb : d241830 p = 1) : d281348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32030 q = 1) (hb : d241830 q = 1) : d281317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d281317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78425 q ha hb
    | true =>
      simp only [d32030, d281317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32031 q = 1) (hb : d241830 q = 1) : d281318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d281318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d281318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32115 q = 1) (hb : d241830 q = 1) : d281345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32115, d281345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32115, d281345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32116 q = 1) (hb : d241830 q = 1) : d281346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32116, d281346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32116, d281346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32117 q = 1) (hb : d241830 q = 1) : d281347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32117, d281347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32117, d281347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32118 q = 1) (hb : d241830 q = 1) : d281348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32118, d281348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32118, d281348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78427 (p : Pattern) (ha : d32124 p = 1) (hb : d241830 p = 1) : d281354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32119 q = 1) (hb : d241830 q = 1) : d281349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32119, d281349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78426 q ha hb
    | true =>
      simp only [d32119, d281349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32120 q = 1) (hb : d241830 q = 1) : d281350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32120, d281350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32120, d281350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32121 q = 1) (hb : d241830 q = 1) : d281351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32121, d281351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32121, d281351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32122 q = 1) (hb : d241830 q = 1) : d281352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32122, d281352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32122, d281352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32123 q = 1) (hb : d241830 q = 1) : d281353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32123, d281353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32123, d281353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32124 q = 1) (hb : d241830 q = 1) : d281354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32124, d281354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32124, d281354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78428 (p : Pattern) (ha : d31720 p = 1) (hb : d241830 p = 1) : d281169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241830 q = 1) : d281142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d241830 q = 1) : d281168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d281168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d281168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31720 q = 1) (hb : d241830 q = 1) : d281169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31720, d281169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31720, d281169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78429 (p : Pattern) (ha : d31722 p = 1) (hb : d241830 p = 1) : d281171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241830 q = 1) : d281146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d241830 q = 1) : d281170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d281170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d281170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31722 q = 1) (hb : d241830 q = 1) : d281171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31722, d281171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31722, d281171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78430 (p : Pattern) (ha : d31729 p = 1) (hb : d241830 p = 1) : d281178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d241830 q = 1) : d281176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d281176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d281176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d241830 q = 1) : d281177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d281177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d281177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31729 q = 1) (hb : d241830 q = 1) : d281178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31729, d281178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31729, d281178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78431 (p : Pattern) (ha : d31732 p = 1) (hb : d241830 p = 1) : d281181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d241830 q = 1) : d281179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d281179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d281179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d241830 q = 1) : d281180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d281180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d281180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31732 q = 1) (hb : d241830 q = 1) : d281181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31732, d281181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31732, d281181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78432 (p : Pattern) (ha : d31761 p = 1) (hb : d241830 p = 1) : d281185 p = 1 := by
  have h0 (q : Pattern) (ha : d31752 q = 1) (hb : d241830 q = 1) : d31752 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31759 q = 1) (hb : d241830 q = 1) : d31759 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31643 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31644 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d31645 q = 1) (hb : d241830 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31646 q = 1) (hb : d241830 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d31760 q = 1) (hb : d241830 q = 1) : d244181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31760, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31760, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31761 q = 1) (hb : d241830 q = 1) : d281185 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31761, d281185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31761, d281185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78433 (p : Pattern) (ha : d31767 p = 1) (hb : d241830 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d241830 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241830 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31765 q = 1) (hb : d241830 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31765, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31765, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d31766 q = 1) (hb : d241830 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31633 q = 1) (hb : d241830 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31634 q = 1) (hb : d241830 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d31635 q = 1) (hb : d241830 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h13 (q : Pattern) (ha : d31767 q = 1) (hb : d241830 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31767, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31767, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro78434 (p : Pattern) (ha : d31773 p = 1) (hb : d241830 p = 1) : d281189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31768 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78433 q ha hb
    | true =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31769 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31770 q = 1) (hb : d241830 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31770, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31770, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31771 q = 1) (hb : d241830 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31771, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31771, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31652 q = 1) (hb : d241830 q = 1) : d281111 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d281111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31653 q = 1) (hb : d241830 q = 1) : d281112 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31653, d281112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31772 q = 1) (hb : d241830 q = 1) : d281113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31772, d281113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31772, d281113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31672 q = 1) (hb : d241830 q = 1) : d281121 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d281121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31672, d281121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31773 q = 1) (hb : d241830 q = 1) : d281189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31773, d281189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31773, d281189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78435 (p : Pattern) (ha : d31779 p = 1) (hb : d241830 p = 1) : d281195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31762 q = 1) (hb : d241830 q = 1) : d281186 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31762, d281186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78432 q ha hb
    | true =>
      simp only [d31762, d281186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78406 q ha hb
  have h2 (q : Pattern) (ha : d31763 q = 1) (hb : d241830 q = 1) : d281187 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31763, d281187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31763, d281187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31764 q = 1) (hb : d241830 q = 1) : d281188 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31764, d281188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31764, d281188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31774 q = 1) (hb : d241830 q = 1) : d281190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31774, d281190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78406 q ha hb
    | true =>
      simp only [d31774, d281190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78434 q ha hb
  have h5 (q : Pattern) (ha : d31775 q = 1) (hb : d241830 q = 1) : d281191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31775, d281191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31775, d281191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31776 q = 1) (hb : d241830 q = 1) : d281192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31776, d281192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31776, d281192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31777 q = 1) (hb : d241830 q = 1) : d281193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31777, d281193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31777, d281193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31674 q = 1) (hb : d241830 q = 1) : d281123 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78406 q ha hb
    | true =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
  have h9 (q : Pattern) (ha : d31675 q = 1) (hb : d241830 q = 1) : d281124 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31676 q = 1) (hb : d241830 q = 1) : d281125 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31679 q = 1) (hb : d241830 q = 1) : d281128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
    | true =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78411 q ha hb
  have h12 (q : Pattern) (ha : d31680 q = 1) (hb : d241830 q = 1) : d281129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31681 q = 1) (hb : d241830 q = 1) : d281130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31682 q = 1) (hb : d241830 q = 1) : d281131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31778 q = 1) (hb : d241830 q = 1) : d281194 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31778, d281194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31778, d281194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31779 q = 1) (hb : d241830 q = 1) : d281195 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31779, d281195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31779, d281195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro78436 (p : Pattern) (ha : d31785 p = 1) (hb : d241830 p = 1) : d281201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d241830 q = 1) : d281196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d281196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78435 q ha hb
    | true =>
      simp only [d31780, d281196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d241830 q = 1) : d281197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d281197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d281197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d241830 q = 1) : d281198 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d281198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d281198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d241830 q = 1) : d281199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d281199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d281199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d241830 q = 1) : d281200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d281200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d281200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31785 q = 1) (hb : d241830 q = 1) : d281201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31785, d281201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31785, d281201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78437 (p : Pattern) (ha : d31878 p = 1) (hb : d241830 p = 1) : d281204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d241830 q = 1) : d281118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d281118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d241830 q = 1) : d281119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d281119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d241830 q = 1) : d281126 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d281126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d281126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31878 q = 1) (hb : d241830 q = 1) : d281204 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31878, d281204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31878, d281204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78438 (p : Pattern) (ha : d31884 p = 1) (hb : d241830 p = 1) : d281210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d241830 q = 1) : d281123 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78406 q ha hb
    | true =>
      simp only [d31674, d281123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d241830 q = 1) : d281124 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d281124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d241830 q = 1) : d281125 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d281125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d241830 q = 1) : d281128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
    | true =>
      simp only [d31679, d281128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78411 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d241830 q = 1) : d281129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d281129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d241830 q = 1) : d281130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d281130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d241830 q = 1) : d281131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d281131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31879 q = 1) (hb : d241830 q = 1) : d281205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31879, d281205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78409 q ha hb
    | true =>
      simp only [d31879, d281205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78437 q ha hb
  have h9 (q : Pattern) (ha : d31880 q = 1) (hb : d241830 q = 1) : d281206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31880, d281206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31880, d281206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31881 q = 1) (hb : d241830 q = 1) : d281207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31881, d281207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31881, d281207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31882 q = 1) (hb : d241830 q = 1) : d281208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31882, d281208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31882, d281208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31883 q = 1) (hb : d241830 q = 1) : d281209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31883, d281209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31883, d281209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31884 q = 1) (hb : d241830 q = 1) : d281210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31884, d281210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31884, d281210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro78439 (p : Pattern) (ha : d31890 p = 1) (hb : d241830 p = 1) : d281216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d241830 q = 1) : d281211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d281211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78438 q ha hb
    | true =>
      simp only [d31885, d281211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d241830 q = 1) : d281212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d281212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d281212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d241830 q = 1) : d281213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d281213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d281213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d241830 q = 1) : d281214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d281214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d281214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d241830 q = 1) : d281215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d281215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d281215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31890 q = 1) (hb : d241830 q = 1) : d281216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31890, d281216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31890, d281216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78440 (p : Pattern) (ha : d241830 p = 1) (hb : d245512 p = 1) : d281222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d241830 q = 1) : d281172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d281172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78428 q ha hb
    | true =>
      simp only [d31723, d281172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78429 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d241830 q = 1) : d281173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d281173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d281173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d241830 q = 1) : d281174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d281174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d281174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d241830 q = 1) : d281175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d281175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d281175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d241830 q = 1) : d281182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d281182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78430 q ha hb
    | true =>
      simp only [d31733, d281182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78431 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d241830 q = 1) : d281183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d281183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d281183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d241830 q = 1) : d281184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d281184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d281184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d241830 q = 1) : d281202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d281202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78436 q ha hb
    | true =>
      simp only [d31786, d281202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78414 q ha hb
  have h9 (q : Pattern) (ha : d241830 q = 1) (hb : d245508 q = 1) : d281203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d281203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245508, d281203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d241830 q = 1) : d281217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d281217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78439 q ha hb
    | true =>
      simp only [d31891, d281217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d241830 q = 1) : d281218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d281218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d281218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241830 q = 1) (hb : d245509 q = 1) : d281219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d281219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d281219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241830 q = 1) (hb : d245510 q = 1) : d281220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d281220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245510, d281220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241830 q = 1) (hb : d245511 q = 1) : d281221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d281221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245511, d281221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d241830 q = 1) (hb : d245512 q = 1) : d281222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d281222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245512, d281222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78441 (p : Pattern) (ha : d31897 p = 1) (hb : d241830 p = 1) : d281223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241830 q = 1) : d281142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d281142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d241830 q = 1) : d281168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d281168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d281168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31897 q = 1) (hb : d241830 q = 1) : d281223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31897, d281223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31897, d281223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78442 (p : Pattern) (ha : d31898 p = 1) (hb : d241830 p = 1) : d281224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241830 q = 1) : d281146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d281146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d241830 q = 1) : d281170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d281170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d281170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31898 q = 1) (hb : d241830 q = 1) : d281224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31898, d281224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31898, d281224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78443 (p : Pattern) (ha : d31903 p = 1) (hb : d241830 p = 1) : d281229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241830 q = 1) : d281141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d281141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d241830 q = 1) : d281176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d281176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d281176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d241830 q = 1) : d281177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d281177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d281177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31903 q = 1) (hb : d241830 q = 1) : d281229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31903, d281229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31903, d281229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78444 (p : Pattern) (ha : d31904 p = 1) (hb : d241830 p = 1) : d281230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241830 q = 1) : d281139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78413 q ha hb
    | true =>
      simp only [d31690, d281139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241830 q = 1) : d281140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d281140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241830 q = 1) : d281145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d281145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d241830 q = 1) : d281179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d281179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d281179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d241830 q = 1) : d281180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d281180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d281180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31904 q = 1) (hb : d241830 q = 1) : d281230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31904, d281230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31904, d281230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78445 (p : Pattern) (ha : d31908 p = 1) (hb : d241830 p = 1) : d281234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d241830 q = 1) : d281196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d281196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78435 q ha hb
    | true =>
      simp only [d31780, d281196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d241830 q = 1) : d281197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d281197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d281197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d241830 q = 1) : d281135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78412 q ha hb
    | true =>
      simp only [d31686, d281135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d241830 q = 1) : d281136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d281136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d241830 q = 1) : d281198 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d281198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d281198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d241830 q = 1) : d281199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d281199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d281199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d241830 q = 1) : d281200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d281200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d281200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31908 q = 1) (hb : d241830 q = 1) : d281234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31908, d281234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31908, d281234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78446 (p : Pattern) (ha : d31914 p = 1) (hb : d241830 p = 1) : d281237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d241830 q = 1) : d281211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d281211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78438 q ha hb
    | true =>
      simp only [d31885, d281211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d241830 q = 1) : d281212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d281212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d281212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d241830 q = 1) : d281213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d281213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d281213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d241830 q = 1) : d281214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d281214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d281214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d241830 q = 1) : d281215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d281215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d281215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31914 q = 1) (hb : d241830 q = 1) : d281237 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31914, d281237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31914, d281237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78447 (p : Pattern) (ha : d241830 p = 1) (hb : d245517 p = 1) : d281243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d241830 q = 1) : d281172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d281172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78428 q ha hb
    | true =>
      simp only [d31723, d281172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78429 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d241830 q = 1) : d281173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d281173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d281173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d241830 q = 1) : d281174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d281174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d281174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d241830 q = 1) : d281175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d281175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d281175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d241830 q = 1) : d281182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d281182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78430 q ha hb
    | true =>
      simp only [d31733, d281182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78431 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d241830 q = 1) : d281183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d281183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d281183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d241830 q = 1) : d281184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d281184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d281184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d241830 q = 1) : d281202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d281202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78436 q ha hb
    | true =>
      simp only [d31786, d281202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78414 q ha hb
  have h9 (q : Pattern) (ha : d241830 q = 1) (hb : d245508 q = 1) : d281203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d281203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245508, d281203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d241830 q = 1) : d281217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d281217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78439 q ha hb
    | true =>
      simp only [d31891, d281217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d241830 q = 1) : d281218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d281218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d281218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241830 q = 1) (hb : d245509 q = 1) : d281219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d281219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d281219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241830 q = 1) (hb : d245510 q = 1) : d281220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d281220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245510, d281220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241830 q = 1) (hb : d245511 q = 1) : d281221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d281221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245511, d281221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31899 q = 1) (hb : d241830 q = 1) : d281225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31899, d281225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78441 q ha hb
    | true =>
      simp only [d31899, d281225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78442 q ha hb
  have h16 (q : Pattern) (ha : d31900 q = 1) (hb : d241830 q = 1) : d281226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31900, d281226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31900, d281226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31901 q = 1) (hb : d241830 q = 1) : d281227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31901, d281227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31901, d281227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31902 q = 1) (hb : d241830 q = 1) : d281228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31902, d281228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31902, d281228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31905 q = 1) (hb : d241830 q = 1) : d281231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31905, d281231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78443 q ha hb
    | true =>
      simp only [d31905, d281231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78444 q ha hb
  have h20 (q : Pattern) (ha : d31906 q = 1) (hb : d241830 q = 1) : d281232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31906, d281232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31906, d281232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31907 q = 1) (hb : d241830 q = 1) : d281233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31907, d281233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31907, d281233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31909 q = 1) (hb : d241830 q = 1) : d281235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d281235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78445 q ha hb
    | true =>
      simp only [d31909, d281235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78417 q ha hb
  have h23 (q : Pattern) (ha : d241830 q = 1) (hb : d245513 q = 1) : d281236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d281236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d245513, d281236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d31915 q = 1) (hb : d241830 q = 1) : d281238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d281238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78446 q ha hb
    | true =>
      simp only [d31915, d281238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31916 q = 1) (hb : d241830 q = 1) : d281239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d281239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31916, d281239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d241830 q = 1) (hb : d245514 q = 1) : d281240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d281240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245514, d281240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d241830 q = 1) (hb : d245515 q = 1) : d281241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d281241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d245515, d281241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d241830 q = 1) (hb : d245516 q = 1) : d281242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d281242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d245516, d281242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d241830 q = 1) (hb : d245517 q = 1) : d281243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d281243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245517, d281243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro78448 (p : Pattern) (ha : d241830 p = 1) (hb : d245524 p = 1) : d281263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31909 q = 1) (hb : d241830 q = 1) : d281235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d281235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78445 q ha hb
    | true =>
      simp only [d31909, d281235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78417 q ha hb
  have h2 (q : Pattern) (ha : d241830 q = 1) (hb : d245513 q = 1) : d281236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d281236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d281236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31915 q = 1) (hb : d241830 q = 1) : d281238 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d281238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78446 q ha hb
    | true =>
      simp only [d31915, d281238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31916 q = 1) (hb : d241830 q = 1) : d281239 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d281239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31916, d281239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241830 q = 1) (hb : d245514 q = 1) : d281240 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d281240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245514, d281240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241830 q = 1) (hb : d245522 q = 1) : d281261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d281261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245522, d281261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241830 q = 1) (hb : d245523 q = 1) : d281262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d281262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245523, d281262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241830 q = 1) (hb : d245524 q = 1) : d281263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d281263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245524, d281263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78449 (p : Pattern) (ha : d31966 p = 1) (hb : d241830 p = 1) : d281271 p = 1 := by
  have h0 (q : Pattern) (ha : d31956 q = 1) (hb : d241830 q = 1) : d31956 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31960 q = 1) (hb : d241830 q = 1) : d31960 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31961 q = 1) (hb : d241830 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
  have h4 (q : Pattern) (ha : d31643 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d31962 q = 1) (hb : d241830 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31644 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d31963 q = 1) (hb : d241830 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31964 q = 1) (hb : d241830 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d31965 q = 1) (hb : d241830 q = 1) : d244255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31965, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31965, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31966 q = 1) (hb : d241830 q = 1) : d281271 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31966, d281271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31966, d281271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro78450 (p : Pattern) (ha : d31981 p = 1) (hb : d241830 p = 1) : d281277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31967 q = 1) (hb : d241830 q = 1) : d31475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31967, d31475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31967, d31475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78402 q ha hb
  have h2 (q : Pattern) (ha : d31627 q = 1) (hb : d241830 q = 1) : d31313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78402 q ha hb
    | true =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31968 q = 1) (hb : d241830 q = 1) : d31476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31968, d31476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31968, d31476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31628 q = 1) (hb : d241830 q = 1) : d31314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31969 q = 1) (hb : d241830 q = 1) : d31477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31969, d31477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31969, d31477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31970 q = 1) (hb : d241830 q = 1) : d31478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31970, d31478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31970, d31478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31971 q = 1) (hb : d241830 q = 1) : d31479 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31971, d31479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31971, d31479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78403 q ha hb
  have h8 (q : Pattern) (ha : d31637 q = 1) (hb : d241830 q = 1) : d31318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78403 q ha hb
    | true =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31972 q = 1) (hb : d241830 q = 1) : d31480 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31972, d31480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31972, d31480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31638 q = 1) (hb : d241830 q = 1) : d31319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31973 q = 1) (hb : d241830 q = 1) : d31481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31973, d31481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31973, d31481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31974 q = 1) (hb : d241830 q = 1) : d31482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31974, d31482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31974, d31482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31975 q = 1) (hb : d241830 q = 1) : d31483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31975, d31483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31975, d31483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31961 q = 1) (hb : d241830 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
  have h15 (q : Pattern) (ha : d31643 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78404 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31962 q = 1) (hb : d241830 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31644 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31963 q = 1) (hb : d241830 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31964 q = 1) (hb : d241830 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31976 q = 1) (hb : d241830 q = 1) : d281272 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
  have h21 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31977 q = 1) (hb : d241830 q = 1) : d281273 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31978 q = 1) (hb : d241830 q = 1) : d281274 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d31979 q = 1) (hb : d241830 q = 1) : d281275 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31980 q = 1) (hb : d241830 q = 1) : d281276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31980, d281276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31980, d281276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31981 q = 1) (hb : d241830 q = 1) : d281277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31981, d281277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31981, d281277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro78451 (p : Pattern) (ha : d31991 p = 1) (hb : d241830 p = 1) : d281282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31985 q = 1) (hb : d241830 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31985, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31985, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78433 q ha hb
  have h2 (q : Pattern) (ha : d31768 q = 1) (hb : d241830 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78433 q ha hb
    | true =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31986 q = 1) (hb : d241830 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31986, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31986, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31769 q = 1) (hb : d241830 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31987 q = 1) (hb : d241830 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31987, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31987, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31988 q = 1) (hb : d241830 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31988, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31988, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31976 q = 1) (hb : d241830 q = 1) : d281272 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d281272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
  have h8 (q : Pattern) (ha : d31650 q = 1) (hb : d241830 q = 1) : d281109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78405 q ha hb
    | true =>
      simp only [d31650, d281109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31977 q = 1) (hb : d241830 q = 1) : d281273 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31977, d281273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31651 q = 1) (hb : d241830 q = 1) : d281110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31651, d281110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31978 q = 1) (hb : d241830 q = 1) : d281274 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31978, d281274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31979 q = 1) (hb : d241830 q = 1) : d281275 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31979, d281275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31989 q = 1) (hb : d241830 q = 1) : d281276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31989, d281276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31989, d281276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31990 q = 1) (hb : d241830 q = 1) : d281281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d281281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31990, d281281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31991 q = 1) (hb : d241830 q = 1) : d281282 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31991, d281282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31991, d281282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78452 (p : Pattern) (ha : d32016 p = 1) (hb : d241830 p = 1) : d281303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31982 q = 1) (hb : d241830 q = 1) : d281278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31982, d281278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78449 q ha hb
    | true =>
      simp only [d31982, d281278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78450 q ha hb
  have h2 (q : Pattern) (ha : d31983 q = 1) (hb : d241830 q = 1) : d281279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31983, d281279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31983, d281279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31984 q = 1) (hb : d241830 q = 1) : d281280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31984, d281280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31984, d281280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31992 q = 1) (hb : d241830 q = 1) : d281283 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31992, d281283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78450 q ha hb
    | true =>
      simp only [d31992, d281283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78451 q ha hb
  have h5 (q : Pattern) (ha : d31993 q = 1) (hb : d241830 q = 1) : d281284 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31993, d281284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31993, d281284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31994 q = 1) (hb : d241830 q = 1) : d281285 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31994, d281285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31994, d281285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31995 q = 1) (hb : d241830 q = 1) : d281286 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31995, d281286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31995, d281286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32006 q = 1) (hb : d241830 q = 1) : d281293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78450 q ha hb
    | true =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
  have h9 (q : Pattern) (ha : d32007 q = 1) (hb : d241830 q = 1) : d281294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32008 q = 1) (hb : d241830 q = 1) : d281295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32011 q = 1) (hb : d241830 q = 1) : d281298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
    | true =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78424 q ha hb
  have h12 (q : Pattern) (ha : d32012 q = 1) (hb : d241830 q = 1) : d281299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32013 q = 1) (hb : d241830 q = 1) : d281300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32014 q = 1) (hb : d241830 q = 1) : d281301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32015 q = 1) (hb : d241830 q = 1) : d281302 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32015, d281302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32015, d281302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32016 q = 1) (hb : d241830 q = 1) : d281303 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32016, d281303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32016, d281303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro78453 (p : Pattern) (ha : d32021 p = 1) (hb : d241830 p = 1) : d281308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d241830 q = 1) : d281293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78450 q ha hb
    | true =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d241830 q = 1) : d281294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d241830 q = 1) : d281295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d241830 q = 1) : d281298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
    | true =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78424 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d241830 q = 1) : d281299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d241830 q = 1) : d281300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d241830 q = 1) : d281301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32019 q = 1) (hb : d241830 q = 1) : d281306 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d281306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32019, d281306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32020 q = 1) (hb : d241830 q = 1) : d281307 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32020, d281307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32020, d281307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32021 q = 1) (hb : d241830 q = 1) : d281308 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32021, d281308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32021, d281308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro78454 (p : Pattern) (ha : d32027 p = 1) (hb : d241830 p = 1) : d281314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32017 q = 1) (hb : d241830 q = 1) : d281304 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32017, d281304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78452 q ha hb
    | true =>
      simp only [d32017, d281304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32018 q = 1) (hb : d241830 q = 1) : d281305 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32018, d281305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32018, d281305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32022 q = 1) (hb : d241830 q = 1) : d281309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d281309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78453 q ha hb
    | true =>
      simp only [d32022, d281309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32023 q = 1) (hb : d241830 q = 1) : d281310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d281310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d281310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32024 q = 1) (hb : d241830 q = 1) : d281311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32024, d281311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32024, d281311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32025 q = 1) (hb : d241830 q = 1) : d281312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32025, d281312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32025, d281312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32026 q = 1) (hb : d241830 q = 1) : d281313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32026, d281313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32026, d281313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32027 q = 1) (hb : d241830 q = 1) : d281314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32027, d281314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32027, d281314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78455 (p : Pattern) (ha : d32035 p = 1) (hb : d241830 p = 1) : d281322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32022 q = 1) (hb : d241830 q = 1) : d281309 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d281309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78453 q ha hb
    | true =>
      simp only [d32022, d281309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32023 q = 1) (hb : d241830 q = 1) : d281310 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d281310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d281310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32030 q = 1) (hb : d241830 q = 1) : d281317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d281317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78425 q ha hb
    | true =>
      simp only [d32030, d281317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32031 q = 1) (hb : d241830 q = 1) : d281318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d281318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d281318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32032 q = 1) (hb : d241830 q = 1) : d281319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32032, d281319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32032, d281319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32033 q = 1) (hb : d241830 q = 1) : d281320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32033, d281320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32033, d281320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32034 q = 1) (hb : d241830 q = 1) : d281321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32034, d281321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32034, d281321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32035 q = 1) (hb : d241830 q = 1) : d281322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32035, d281322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32035, d281322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78456 (p : Pattern) (ha : d32095 p = 1) (hb : d241830 p = 1) : d281325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d241830 q = 1) : d281287 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d281287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d241830 q = 1) : d281116 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78408 q ha hb
    | true =>
      simp only [d31667, d281116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d241830 q = 1) : d281288 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d281288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d241830 q = 1) : d281117 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d281117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d241830 q = 1) : d281289 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d281289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d241830 q = 1) : d281290 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d281290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d241830 q = 1) : d281296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d281296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d281296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32095 q = 1) (hb : d241830 q = 1) : d281325 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32095, d281325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32095, d281325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78457 (p : Pattern) (ha : d32101 p = 1) (hb : d241830 p = 1) : d281331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d241830 q = 1) : d281293 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78450 q ha hb
    | true =>
      simp only [d32006, d281293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d241830 q = 1) : d281294 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d281294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d241830 q = 1) : d281295 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d281295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d241830 q = 1) : d281298 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
    | true =>
      simp only [d32011, d281298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78424 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d241830 q = 1) : d281299 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d281299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d241830 q = 1) : d281300 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d281300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d241830 q = 1) : d281301 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d281301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32096 q = 1) (hb : d241830 q = 1) : d281326 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32096, d281326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78423 q ha hb
    | true =>
      simp only [d32096, d281326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78456 q ha hb
  have h9 (q : Pattern) (ha : d32097 q = 1) (hb : d241830 q = 1) : d281327 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32097, d281327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32097, d281327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32098 q = 1) (hb : d241830 q = 1) : d281328 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32098, d281328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32098, d281328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32099 q = 1) (hb : d241830 q = 1) : d281329 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32099, d281329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32099, d281329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32100 q = 1) (hb : d241830 q = 1) : d281330 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32100, d281330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32100, d281330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32101 q = 1) (hb : d241830 q = 1) : d281331 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32101, d281331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32101, d281331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro78458 (p : Pattern) (ha : d32107 p = 1) (hb : d241830 p = 1) : d281337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32102 q = 1) (hb : d241830 q = 1) : d281332 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32102, d281332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78457 q ha hb
    | true =>
      simp only [d32102, d281332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32103 q = 1) (hb : d241830 q = 1) : d281333 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32103, d281333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32103, d281333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32104 q = 1) (hb : d241830 q = 1) : d281334 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32104, d281334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32104, d281334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32105 q = 1) (hb : d241830 q = 1) : d281335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32105, d281335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32105, d281335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32106 q = 1) (hb : d241830 q = 1) : d281336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32106, d281336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32106, d281336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32107 q = 1) (hb : d241830 q = 1) : d281337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32107, d281337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32107, d281337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78459 (p : Pattern) (ha : d241830 p = 1) (hb : d245534 p = 1) : d281343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32036 q = 1) (hb : d241830 q = 1) : d281323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32036, d281323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78454 q ha hb
    | true =>
      simp only [d32036, d281323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78455 q ha hb
  have h2 (q : Pattern) (ha : d241830 q = 1) (hb : d245530 q = 1) : d281324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d281324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d281324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d32108 q = 1) (hb : d241830 q = 1) : d281338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32108, d281338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78458 q ha hb
    | true =>
      simp only [d32108, d281338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32109 q = 1) (hb : d241830 q = 1) : d281339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32109, d281339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32109, d281339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241830 q = 1) (hb : d245531 q = 1) : d281340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d281340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245531, d281340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241830 q = 1) (hb : d245532 q = 1) : d281341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d281341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245532, d281341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241830 q = 1) (hb : d245533 q = 1) : d281342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d281342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245533, d281342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241830 q = 1) (hb : d245534 q = 1) : d281343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d281343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245534, d281343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78460 (p : Pattern) (ha : d241830 p = 1) (hb : d245540 p = 1) : d281360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31706 q = 1) (hb : d241830 q = 1) : d281155 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31706, d281155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31706, d281155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78416 q ha hb
  have h2 (q : Pattern) (ha : d31707 q = 1) (hb : d241830 q = 1) : d281156 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31707, d281156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31707, d281156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31716 q = 1) (hb : d241830 q = 1) : d281165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78416 q ha hb
    | true =>
      simp only [d31716, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78419 q ha hb
  have h4 (q : Pattern) (ha : d31717 q = 1) (hb : d241830 q = 1) : d281166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31717, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31718 q = 1) (hb : d241830 q = 1) : d281167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d31718, d281167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31718, d281167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241830 q = 1) (hb : d245518 q = 1) : d281244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d281244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78440 q ha hb
    | true =>
      simp only [d245518, d281244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78447 q ha hb
  have h7 (q : Pattern) (ha : d31934 q = 1) (hb : d241830 q = 1) : d281257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31934, d281257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78420 q ha hb
    | true =>
      simp only [d31934, d281257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78421 q ha hb
  have h8 (q : Pattern) (ha : d241830 q = 1) (hb : d245519 q = 1) : d281258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d281258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245519, d281258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d241830 q = 1) (hb : d245520 q = 1) : d281259 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d281259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245520, d281259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d241830 q = 1) (hb : d245521 q = 1) : d281260 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d281260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245521, d281260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241830 q = 1) (hb : d245525 q = 1) : d281264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d281264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245525, d281264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78448 q ha hb
  have h12 (q : Pattern) (ha : d31943 q = 1) (hb : d241830 q = 1) : d281266 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31943, d281266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31943, d281266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78422 q ha hb
  have h13 (q : Pattern) (ha : d241830 q = 1) (hb : d245526 q = 1) : d281267 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d281267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245526, d281267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d241830 q = 1) (hb : d245527 q = 1) : d281268 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d281268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245527, d281268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241830 q = 1) (hb : d245528 q = 1) : d281269 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d281269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245528, d281269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d241830 q = 1) (hb : d245529 q = 1) : d281270 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d281270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245529, d281270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d241830 q = 1) (hb : d245535 q = 1) : d281344 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d281344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245535, d281344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78459 q ha hb
  have h18 (q : Pattern) (ha : d32125 q = 1) (hb : d241830 q = 1) : d281355 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32125, d281355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32125, d281355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78427 q ha hb
  have h19 (q : Pattern) (ha : d241830 q = 1) (hb : d245536 q = 1) : d281356 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d281356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245536, d281356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d241830 q = 1) (hb : d245537 q = 1) : d281357 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d281357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245537, d281357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d241830 q = 1) (hb : d245538 q = 1) : d281358 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d281358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245538, d281358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d241830 q = 1) (hb : d245539 q = 1) : d281359 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d281359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245539, d281359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d241830 q = 1) (hb : d245540 q = 1) : d281360 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d281360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245540, d281360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro78461 (p : Pattern) (ha : d241830 p = 1) (hb : d245546 p = 1) : d281366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241830 q = 1) (hb : d245541 q = 1) : d281361 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d281361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245541, d281361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78460 q ha hb
  have h2 (q : Pattern) (ha : d241830 q = 1) (hb : d245542 q = 1) : d281362 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d281362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245542, d281362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241830 q = 1) (hb : d245543 q = 1) : d281363 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d281363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245543, d281363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241830 q = 1) (hb : d245544 q = 1) : d281364 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d281364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245544, d281364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241830 q = 1) (hb : d245545 q = 1) : d281365 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d281365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245545, d281365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241830 q = 1) (hb : d245546 q = 1) : d281366 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d281366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245546, d281366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78462 (p : Pattern) (ha : d32146 p = 1) (hb : d241830 p = 1) : d281372 p = 1 := by
  have h0 (q : Pattern) (ha : d31738 q = 1) (hb : d241830 q = 1) : d31738 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31304 q = 1) (hb : d241830 q = 1) : d31304 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32143 q = 1) (hb : d241830 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31739 q = 1) (hb : d241830 q = 1) : d31739 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32144 q = 1) (hb : d241830 q = 1) : d281370 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32144, d281370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32144, d281370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32145 q = 1) (hb : d241830 q = 1) : d281371 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32145, d281371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32145, d281371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d32146 q = 1) (hb : d241830 q = 1) : d281372 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32146, d281372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32146, d281372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78463 (p : Pattern) (ha : d32160 p = 1) (hb : d241830 p = 1) : d281382 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d241830 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241830 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31306 q = 1) (hb : d241830 q = 1) : d31306 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32151 q = 1) (hb : d241830 q = 1) : d281377 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32152 q = 1) (hb : d241830 q = 1) : d281378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25766 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d32157 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d32158 q = 1) (hb : d241830 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d32159 q = 1) (hb : d241830 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h20 (q : Pattern) (ha : d32160 q = 1) (hb : d241830 q = 1) : d281382 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32160, d281382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32160, d281382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro78464 (p : Pattern) (ha : d32171 p = 1) (hb : d241830 p = 1) : d281388 p = 1 := by
  have h0 (q : Pattern) (ha : d32170 q = 1) (hb : d241830 q = 1) : d32170 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25766 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32157 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32158 q = 1) (hb : d241830 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32159 q = 1) (hb : d241830 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h13 (q : Pattern) (ha : d32171 q = 1) (hb : d241830 q = 1) : d281388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32171, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32171, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro78465 (p : Pattern) (ha : d32180 p = 1) (hb : d241830 p = 1) : d281395 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25766 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32157 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25767 q = 1) (hb : d241830 q = 1) : d25767 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32176 q = 1) (hb : d241830 q = 1) : d281393 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32177 q = 1) (hb : d241830 q = 1) : d281394 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1559 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1575 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d1576 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1565 q = 1) (hb : d241830 q = 1) : d1565 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1577 q = 1) (hb : d241830 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1577, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10131 q = 1) (hb : d241830 q = 1) : d10131 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d32178 q = 1) (hb : d241830 q = 1) : d29565 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d29565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32178, d29565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d32179 q = 1) (hb : d241830 q = 1) : d29566 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d29566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d32179, d29566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h23 (q : Pattern) (ha : d32180 q = 1) (hb : d241830 q = 1) : d281395 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32180, d281395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32180, d281395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro78466 (p : Pattern) (ha : d32186 p = 1) (hb : d241830 p = 1) : d281401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32147 q = 1) (hb : d241830 q = 1) : d281373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78462 q ha hb
    | true =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32148 q = 1) (hb : d241830 q = 1) : d281374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32149 q = 1) (hb : d241830 q = 1) : d281375 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32149, d281375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32149, d281375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32150 q = 1) (hb : d241830 q = 1) : d281376 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32150, d281376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32150, d281376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32161 q = 1) (hb : d241830 q = 1) : d281383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78463 q ha hb
    | true =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32162 q = 1) (hb : d241830 q = 1) : d281384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32163 q = 1) (hb : d241830 q = 1) : d281385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32163, d281385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32163, d281385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32164 q = 1) (hb : d241830 q = 1) : d281386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32164, d281386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32164, d281386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32165 q = 1) (hb : d241830 q = 1) : d281387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32165, d281387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32165, d281387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32172 q = 1) (hb : d241830 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78464 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32173 q = 1) (hb : d241830 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32174 q = 1) (hb : d241830 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32175 q = 1) (hb : d241830 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32181 q = 1) (hb : d241830 q = 1) : d281396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78465 q ha hb
    | true =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32182 q = 1) (hb : d241830 q = 1) : d281397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32183 q = 1) (hb : d241830 q = 1) : d281398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32184 q = 1) (hb : d241830 q = 1) : d281399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32185 q = 1) (hb : d241830 q = 1) : d281400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32185, d281400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32185, d281400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32186 q = 1) (hb : d241830 q = 1) : d281401 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32186, d281401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32186, d281401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78467 (p : Pattern) (ha : d32193 p = 1) (hb : d241830 p = 1) : d281404 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d241830 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241830 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31306 q = 1) (hb : d241830 q = 1) : d31306 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32151 q = 1) (hb : d241830 q = 1) : d281377 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32152 q = 1) (hb : d241830 q = 1) : d281378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25764 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d32187 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d32188 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h20 (q : Pattern) (ha : d32189 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d32190 q = 1) (hb : d241830 q = 1) : d32190 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d32191 q = 1) (hb : d241830 q = 1) : d281402 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d32192 q = 1) (hb : d241830 q = 1) : d281403 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h24 (q : Pattern) (ha : d32193 q = 1) (hb : d241830 q = 1) : d281404 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32193, d281404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32193, d281404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro78468 (p : Pattern) (ha : d32198 p = 1) (hb : d241830 p = 1) : d281409 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25764 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32187 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32188 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32189 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32190 q = 1) (hb : d241830 q = 1) : d32190 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32191 q = 1) (hb : d241830 q = 1) : d281402 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32192 q = 1) (hb : d241830 q = 1) : d281403 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d1559 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1575 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d1576 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1565 q = 1) (hb : d241830 q = 1) : d1565 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1577 q = 1) (hb : d241830 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1577, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10131 q = 1) (hb : d241830 q = 1) : d10131 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d32178 q = 1) (hb : d241830 q = 1) : d29565 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d29565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d32178, d29565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d32179 q = 1) (hb : d241830 q = 1) : d29566 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d29566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d32179, d29566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h26 (q : Pattern) (ha : d32198 q = 1) (hb : d241830 q = 1) : d281409 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32198, d281409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32198, d281409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  exact h26 p ha hb
theorem andIntro78469 (p : Pattern) (ha : d32205 p = 1) (hb : d241830 p = 1) : d281416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d241830 q = 1) : d281405 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78467 q ha hb
    | true =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d241830 q = 1) : d281406 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d241830 q = 1) : d281407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d281407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d281407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d241830 q = 1) : d281408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d281408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d281408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d241830 q = 1) : d281410 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
    | true =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d241830 q = 1) : d281411 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d241830 q = 1) : d281412 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d241830 q = 1) : d281413 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d241830 q = 1) : d281414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d281414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d281414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32181 q = 1) (hb : d241830 q = 1) : d281396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78465 q ha hb
    | true =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32182 q = 1) (hb : d241830 q = 1) : d281397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32183 q = 1) (hb : d241830 q = 1) : d281398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32184 q = 1) (hb : d241830 q = 1) : d281399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32204 q = 1) (hb : d241830 q = 1) : d281415 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d281415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32204, d281415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32205 q = 1) (hb : d241830 q = 1) : d281416 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32205, d281416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32205, d281416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78470 (p : Pattern) (ha : d10134 p = 1) (hb : d241830 p = 1) : d29595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1559 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1575 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1575, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1115 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1576 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1593 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10131 q = 1) (hb : d241830 q = 1) : d10131 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10132 q = 1) (hb : d241830 q = 1) : d29593 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d29593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10132, d29593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10133 q = 1) (hb : d241830 q = 1) : d29594 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d29594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10133, d29594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h11 (q : Pattern) (ha : d10134 q = 1) (hb : d241830 q = 1) : d29595 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d29595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10134, d29595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h11 p ha hb
theorem andIntro78471 (p : Pattern) (ha : d32210 p = 1) (hb : d241830 p = 1) : d281421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32199 q = 1) (hb : d241830 q = 1) : d281410 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
    | true =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32200 q = 1) (hb : d241830 q = 1) : d281411 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32201 q = 1) (hb : d241830 q = 1) : d281412 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32202 q = 1) (hb : d241830 q = 1) : d281413 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32209 q = 1) (hb : d241830 q = 1) : d281420 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32209, d281420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32209, d281420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d241830 q = 1) : d29596 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d29596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78470 q ha hb
    | true =>
      simp only [d10135, d29596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d241830 q = 1) : d29597 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d29597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d29597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d241830 q = 1) : d29598 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d29598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d29598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d241830 q = 1) : d29599 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d29599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d29599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d241830 q = 1) : d29600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d29600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d29600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32210 q = 1) (hb : d241830 q = 1) : d281421 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32210, d281421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32210, d281421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78472 (p : Pattern) (ha : d32217 p = 1) (hb : d241830 p = 1) : d281428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32206 q = 1) (hb : d241830 q = 1) : d281417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d281417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78466 q ha hb
    | true =>
      simp only [d32206, d281417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78469 q ha hb
  have h2 (q : Pattern) (ha : d32207 q = 1) (hb : d241830 q = 1) : d281418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d281418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d281418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32208 q = 1) (hb : d241830 q = 1) : d281419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d281419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d281419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32211 q = 1) (hb : d241830 q = 1) : d281422 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78469 q ha hb
    | true =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78471 q ha hb
  have h5 (q : Pattern) (ha : d32212 q = 1) (hb : d241830 q = 1) : d281423 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32213 q = 1) (hb : d241830 q = 1) : d281424 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32214 q = 1) (hb : d241830 q = 1) : d281425 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d281425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32214, d281425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32215 q = 1) (hb : d241830 q = 1) : d281426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d281426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32215, d281426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32216 q = 1) (hb : d241830 q = 1) : d281427 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32216, d281427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32216, d281427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32217 q = 1) (hb : d241830 q = 1) : d281428 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32217, d281428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32217, d281428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro78473 (p : Pattern) (ha : d32221 p = 1) (hb : d241830 p = 1) : d281432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32211 q = 1) (hb : d241830 q = 1) : d281422 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78469 q ha hb
    | true =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78471 q ha hb
  have h2 (q : Pattern) (ha : d32212 q = 1) (hb : d241830 q = 1) : d281423 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32213 q = 1) (hb : d241830 q = 1) : d281424 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32215 q = 1) (hb : d241830 q = 1) : d281426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d281426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32215, d281426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32220 q = 1) (hb : d241830 q = 1) : d281431 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32220, d281431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32220, d281431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32221 q = 1) (hb : d241830 q = 1) : d281432 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32221, d281432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32221, d281432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78474 (p : Pattern) (ha : d32227 p = 1) (hb : d241830 p = 1) : d281438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241830 q = 1) : d281429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78472 q ha hb
    | true =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241830 q = 1) : d281430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241830 q = 1) : d281435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241830 q = 1) : d281436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d241830 q = 1) : d281437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d281437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d281437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32227 q = 1) (hb : d241830 q = 1) : d281438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32227, d281438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32227, d281438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78475 (p : Pattern) (ha : d32231 p = 1) (hb : d241830 p = 1) : d281442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241830 q = 1) : d281439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241830 q = 1) : d281440 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d241830 q = 1) : d281441 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d281441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d281441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32231 q = 1) (hb : d241830 q = 1) : d281442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32231, d281442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32231, d281442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78476 (p : Pattern) (ha : d32237 p = 1) (hb : d241830 p = 1) : d281448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241830 q = 1) : d281443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78474 q ha hb
    | true =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78475 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241830 q = 1) : d281444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241830 q = 1) : d281445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241830 q = 1) : d281446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241830 q = 1) : d281447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32237 q = 1) (hb : d241830 q = 1) : d281448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32237, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32237, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78477 (p : Pattern) (ha : d32240 p = 1) (hb : d241830 p = 1) : d281451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241830 q = 1) : d281429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78472 q ha hb
    | true =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241830 q = 1) : d281430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241830 q = 1) : d281435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241830 q = 1) : d281436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d241830 q = 1) : d281437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d281437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d281437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32240 q = 1) (hb : d241830 q = 1) : d281451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32240, d281451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32240, d281451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro78478 (p : Pattern) (ha : d32241 p = 1) (hb : d241830 p = 1) : d281452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241830 q = 1) : d281439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241830 q = 1) : d281440 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d241830 q = 1) : d281441 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d281441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d281441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32241 q = 1) (hb : d241830 q = 1) : d281452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32241, d281452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32241, d281452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78479 (p : Pattern) (ha : d32247 p = 1) (hb : d241830 p = 1) : d281458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241830 q = 1) : d281443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78474 q ha hb
    | true =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78475 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241830 q = 1) : d281444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241830 q = 1) : d281445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241830 q = 1) : d281446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241830 q = 1) : d281447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32242 q = 1) (hb : d241830 q = 1) : d281453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d281453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78477 q ha hb
    | true =>
      simp only [d32242, d281453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78478 q ha hb
  have h7 (q : Pattern) (ha : d32243 q = 1) (hb : d241830 q = 1) : d281454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32244 q = 1) (hb : d241830 q = 1) : d281455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32244, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32245 q = 1) (hb : d241830 q = 1) : d281456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32246 q = 1) (hb : d241830 q = 1) : d281457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32247 q = 1) (hb : d241830 q = 1) : d281458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32247, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32247, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78480 (p : Pattern) (ha : d32466 p = 1) (hb : d241830 p = 1) : d281558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241830 q = 1) : d281443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78474 q ha hb
    | true =>
      simp only [d32232, d281443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78475 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241830 q = 1) : d281444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241830 q = 1) : d281445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241830 q = 1) : d281446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241830 q = 1) : d281447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32461 q = 1) (hb : d241830 q = 1) : d281553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d281553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78475 q ha hb
    | true =>
      simp only [d32461, d281553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32462 q = 1) (hb : d241830 q = 1) : d281554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d281554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d281554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32463 q = 1) (hb : d241830 q = 1) : d281555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d281555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32463, d281555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32464 q = 1) (hb : d241830 q = 1) : d281556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d281556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d281556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32465 q = 1) (hb : d241830 q = 1) : d281557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d281557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d281557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32466 q = 1) (hb : d241830 q = 1) : d281558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32466, d281558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32466, d281558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78481 (p : Pattern) (ha : d32472 p = 1) (hb : d241830 p = 1) : d281564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32461 q = 1) (hb : d241830 q = 1) : d281553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d281553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78475 q ha hb
    | true =>
      simp only [d32461, d281553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32462 q = 1) (hb : d241830 q = 1) : d281554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d281554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d281554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32463 q = 1) (hb : d241830 q = 1) : d281555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d281555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32463, d281555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32464 q = 1) (hb : d241830 q = 1) : d281556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d281556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d281556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32465 q = 1) (hb : d241830 q = 1) : d281557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d281557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d281557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32467 q = 1) (hb : d241830 q = 1) : d281559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d281559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78478 q ha hb
    | true =>
      simp only [d32467, d281559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32468 q = 1) (hb : d241830 q = 1) : d281560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d281560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d281560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32469 q = 1) (hb : d241830 q = 1) : d281561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d281561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32469, d281561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32470 q = 1) (hb : d241830 q = 1) : d281562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d281562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d281562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32471 q = 1) (hb : d241830 q = 1) : d281563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d281563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d281563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32472 q = 1) (hb : d241830 q = 1) : d281564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32472, d281564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32472, d281564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78482 (p : Pattern) (ha : d32481 p = 1) (hb : d241830 p = 1) : d281573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32467 q = 1) (hb : d241830 q = 1) : d281559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d281559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78478 q ha hb
    | true =>
      simp only [d32467, d281559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32468 q = 1) (hb : d241830 q = 1) : d281560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d281560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d281560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32469 q = 1) (hb : d241830 q = 1) : d281561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d281561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32469, d281561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32470 q = 1) (hb : d241830 q = 1) : d281562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d281562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d281562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32471 q = 1) (hb : d241830 q = 1) : d281563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d281563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d281563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32481 q = 1) (hb : d241830 q = 1) : d281573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32481, d281573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32481, d281573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78483 (p : Pattern) (ha : d32540 p = 1) (hb : d241830 p = 1) : d281618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32531 q = 1) (hb : d241830 q = 1) : d281609 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32531, d281609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32531, d281609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78467 q ha hb
  have h2 (q : Pattern) (ha : d32194 q = 1) (hb : d241830 q = 1) : d281405 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78467 q ha hb
    | true =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32532 q = 1) (hb : d241830 q = 1) : d281610 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32532, d281610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32532, d281610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32195 q = 1) (hb : d241830 q = 1) : d281406 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32533 q = 1) (hb : d241830 q = 1) : d281611 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32533, d281611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32533, d281611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32534 q = 1) (hb : d241830 q = 1) : d281612 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32534, d281612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32534, d281612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32535 q = 1) (hb : d241830 q = 1) : d281613 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d281613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d281613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
  have h8 (q : Pattern) (ha : d32199 q = 1) (hb : d241830 q = 1) : d281410 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
    | true =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32536 q = 1) (hb : d241830 q = 1) : d281614 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d281614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32536, d281614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32200 q = 1) (hb : d241830 q = 1) : d281411 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32537 q = 1) (hb : d241830 q = 1) : d281615 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d281615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32537, d281615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32538 q = 1) (hb : d241830 q = 1) : d281616 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d281616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32538, d281616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32539 q = 1) (hb : d241830 q = 1) : d281617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32539, d281617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32539, d281617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32511 q = 1) (hb : d241830 q = 1) : d281594 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32511, d281594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32511, d281594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78465 q ha hb
  have h15 (q : Pattern) (ha : d32181 q = 1) (hb : d241830 q = 1) : d281396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78465 q ha hb
    | true =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32512 q = 1) (hb : d241830 q = 1) : d281595 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32512, d281595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32512, d281595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32182 q = 1) (hb : d241830 q = 1) : d281397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32513 q = 1) (hb : d241830 q = 1) : d281596 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32513, d281596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32513, d281596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32514 q = 1) (hb : d241830 q = 1) : d281597 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32514, d281597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32514, d281597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32525 q = 1) (hb : d241830 q = 1) : d281603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32525, d281603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32525, d281603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32540 q = 1) (hb : d241830 q = 1) : d281618 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32540, d281618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32540, d281618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro78484 (p : Pattern) (ha : d32545 p = 1) (hb : d241830 p = 1) : d281623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32535 q = 1) (hb : d241830 q = 1) : d281613 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d281613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d281613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
  have h2 (q : Pattern) (ha : d32199 q = 1) (hb : d241830 q = 1) : d281410 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
    | true =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32536 q = 1) (hb : d241830 q = 1) : d281614 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d281614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32536, d281614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32200 q = 1) (hb : d241830 q = 1) : d281411 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32537 q = 1) (hb : d241830 q = 1) : d281615 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d281615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32537, d281615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32538 q = 1) (hb : d241830 q = 1) : d281616 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d281616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32538, d281616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32544 q = 1) (hb : d241830 q = 1) : d281622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32544, d281622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32544, d281622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d241830 q = 1) : d29925 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d29925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d29925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78470 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d241830 q = 1) : d29596 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d29596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78470 q ha hb
    | true =>
      simp only [d10135, d29596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d241830 q = 1) : d29926 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d29926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d29926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d241830 q = 1) : d29597 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d29597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d29597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d241830 q = 1) : d29927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d29927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d29927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d241830 q = 1) : d29928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d29928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d29928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d241830 q = 1) : d29929 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d29929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d29929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32545 q = 1) (hb : d241830 q = 1) : d281623 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32545, d281623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32545, d281623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78485 (p : Pattern) (ha : d32564 p = 1) (hb : d241830 p = 1) : d281642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32546 q = 1) (hb : d241830 q = 1) : d281624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d281624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78483 q ha hb
    | true =>
      simp only [d32546, d281624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78484 q ha hb
  have h2 (q : Pattern) (ha : d32547 q = 1) (hb : d241830 q = 1) : d281625 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d281625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d281625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32548 q = 1) (hb : d241830 q = 1) : d281626 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d281626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d281626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32554 q = 1) (hb : d241830 q = 1) : d281632 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32554, d281632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32554, d281632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32563 q = 1) (hb : d241830 q = 1) : d281641 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32563, d281641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32563, d281641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32564 q = 1) (hb : d241830 q = 1) : d281642 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32564, d281642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32564, d281642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78486 (p : Pattern) (ha : d32664 p = 1) (hb : d241830 p = 1) : d281685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32565 q = 1) (hb : d241830 q = 1) : d281643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32565, d281643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78485 q ha hb
    | true =>
      simp only [d32565, d281643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32566 q = 1) (hb : d241830 q = 1) : d281644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32566, d281644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32566, d281644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32661 q = 1) (hb : d241830 q = 1) : d281682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32661, d281682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32661, d281682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32662 q = 1) (hb : d241830 q = 1) : d281683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32662, d281683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32662, d281683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32663 q = 1) (hb : d241830 q = 1) : d281684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32663, d281684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32663, d281684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32664 q = 1) (hb : d241830 q = 1) : d281685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32664, d281685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32664, d281685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro78487 (p : Pattern) (ha : d32670 p = 1) (hb : d241830 p = 1) : d281691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32665 q = 1) (hb : d241830 q = 1) : d281686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32665, d281686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78486 q ha hb
    | true =>
      simp only [d32665, d281686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32666 q = 1) (hb : d241830 q = 1) : d281687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32666, d281687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32666, d281687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32667 q = 1) (hb : d241830 q = 1) : d281688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32667, d281688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32667, d281688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32668 q = 1) (hb : d241830 q = 1) : d281689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32668, d281689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32668, d281689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32669 q = 1) (hb : d241830 q = 1) : d281690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32669, d281690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32669, d281690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32670 q = 1) (hb : d241830 q = 1) : d281691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32670, d281691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32670, d281691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78488 (p : Pattern) (ha : d32252 p = 1) (hb : d241830 p = 1) : d281463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241830 q = 1) : d281429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78472 q ha hb
    | true =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241830 q = 1) : d281430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241830 q = 1) : d281435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241830 q = 1) : d281436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d281436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32251 q = 1) (hb : d241830 q = 1) : d281462 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32251, d281462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32251, d281462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32252 q = 1) (hb : d241830 q = 1) : d281463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32252, d281463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32252, d281463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78489 (p : Pattern) (ha : d32254 p = 1) (hb : d241830 p = 1) : d281465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241830 q = 1) : d281439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241830 q = 1) : d281440 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d281440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32253 q = 1) (hb : d241830 q = 1) : d281464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32253, d281464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32253, d281464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32254 q = 1) (hb : d241830 q = 1) : d281465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32254, d281465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32254, d281465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78490 (p : Pattern) (ha : d32261 p = 1) (hb : d241830 p = 1) : d281472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241830 q = 1) : d281429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78472 q ha hb
    | true =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241830 q = 1) : d281430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241830 q = 1) : d281435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d281435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32259 q = 1) (hb : d241830 q = 1) : d281470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32259, d281470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32259, d281470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32260 q = 1) (hb : d241830 q = 1) : d281471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32260, d281471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32260, d281471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32261 q = 1) (hb : d241830 q = 1) : d281472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32261, d281472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32261, d281472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78491 (p : Pattern) (ha : d32264 p = 1) (hb : d241830 p = 1) : d281475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241830 q = 1) : d281433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78473 q ha hb
    | true =>
      simp only [d32222, d281433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241830 q = 1) : d281434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d281434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241830 q = 1) : d281439 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d281439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32262 q = 1) (hb : d241830 q = 1) : d281473 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32262, d281473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32262, d281473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32263 q = 1) (hb : d241830 q = 1) : d281474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32263, d281474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32263, d281474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32264 q = 1) (hb : d241830 q = 1) : d281475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32264, d281475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32264, d281475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro78492 (p : Pattern) (ha : d32280 p = 1) (hb : d241830 p = 1) : d281480 p = 1 := by
  have h0 (q : Pattern) (ha : d32278 q = 1) (hb : d241830 q = 1) : d32278 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32277 q = 1) (hb : d241830 q = 1) : d32277 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32172 q = 1) (hb : d241830 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78464 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32173 q = 1) (hb : d241830 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d32174 q = 1) (hb : d241830 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32175 q = 1) (hb : d241830 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d32279 q = 1) (hb : d241830 q = 1) : d281479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32279, d281479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32279, d281479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32280 q = 1) (hb : d241830 q = 1) : d281480 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32280, d281480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32280, d281480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78493 (p : Pattern) (ha : d32286 p = 1) (hb : d241830 p = 1) : d281388 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d241830 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241830 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32284 q = 1) (hb : d241830 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32284, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32284, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d32285 q = 1) (hb : d241830 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25766 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d32157 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32158 q = 1) (hb : d241830 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d32159 q = 1) (hb : d241830 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d32286 q = 1) (hb : d241830 q = 1) : d281388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32286, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32286, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro78494 (p : Pattern) (ha : d32292 p = 1) (hb : d241830 p = 1) : d281484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32287 q = 1) (hb : d241830 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78493 q ha hb
    | true =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32288 q = 1) (hb : d241830 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32289 q = 1) (hb : d241830 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32289, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32289, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32290 q = 1) (hb : d241830 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32290, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32290, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32181 q = 1) (hb : d241830 q = 1) : d281396 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78465 q ha hb
    | true =>
      simp only [d32181, d281396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32182 q = 1) (hb : d241830 q = 1) : d281397 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32182, d281397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32183 q = 1) (hb : d241830 q = 1) : d281398 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d281398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32184 q = 1) (hb : d241830 q = 1) : d281399 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32184, d281399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32291 q = 1) (hb : d241830 q = 1) : d281400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32291, d281400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32291, d281400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32204 q = 1) (hb : d241830 q = 1) : d281415 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d281415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32204, d281415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32292 q = 1) (hb : d241830 q = 1) : d281484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32292, d281484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32292, d281484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro78495 (p : Pattern) (ha : d32298 p = 1) (hb : d241830 p = 1) : d281490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32281 q = 1) (hb : d241830 q = 1) : d281481 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32281, d281481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78492 q ha hb
    | true =>
      simp only [d32281, d281481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78466 q ha hb
  have h2 (q : Pattern) (ha : d32282 q = 1) (hb : d241830 q = 1) : d281482 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32282, d281482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32282, d281482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32283 q = 1) (hb : d241830 q = 1) : d281483 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32283, d281483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32283, d281483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32293 q = 1) (hb : d241830 q = 1) : d281485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32293, d281485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78466 q ha hb
    | true =>
      simp only [d32293, d281485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78494 q ha hb
  have h5 (q : Pattern) (ha : d32294 q = 1) (hb : d241830 q = 1) : d281486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32294, d281486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32294, d281486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32295 q = 1) (hb : d241830 q = 1) : d281487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32295, d281487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32295, d281487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32296 q = 1) (hb : d241830 q = 1) : d281488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32296, d281488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32296, d281488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32206 q = 1) (hb : d241830 q = 1) : d281417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d281417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78466 q ha hb
    | true =>
      simp only [d32206, d281417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78469 q ha hb
  have h9 (q : Pattern) (ha : d32207 q = 1) (hb : d241830 q = 1) : d281418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d281418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d281418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32208 q = 1) (hb : d241830 q = 1) : d281419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d281419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d281419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32211 q = 1) (hb : d241830 q = 1) : d281422 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78469 q ha hb
    | true =>
      simp only [d32211, d281422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78471 q ha hb
  have h12 (q : Pattern) (ha : d32212 q = 1) (hb : d241830 q = 1) : d281423 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d281423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32213 q = 1) (hb : d241830 q = 1) : d281424 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d281424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32214 q = 1) (hb : d241830 q = 1) : d281425 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d281425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32214, d281425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32297 q = 1) (hb : d241830 q = 1) : d281489 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32297, d281489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32297, d281489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32298 q = 1) (hb : d241830 q = 1) : d281490 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32298, d281490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32298, d281490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro78496 (p : Pattern) (ha : d32304 p = 1) (hb : d241830 p = 1) : d281496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32299 q = 1) (hb : d241830 q = 1) : d281491 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32299, d281491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78495 q ha hb
    | true =>
      simp only [d32299, d281491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32300 q = 1) (hb : d241830 q = 1) : d281492 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32300, d281492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32300, d281492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32218 q = 1) (hb : d241830 q = 1) : d281429 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78472 q ha hb
    | true =>
      simp only [d32218, d281429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32219 q = 1) (hb : d241830 q = 1) : d281430 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d281430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32301 q = 1) (hb : d241830 q = 1) : d281493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32301, d281493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32301, d281493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32302 q = 1) (hb : d241830 q = 1) : d281494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32302, d281494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32302, d281494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32303 q = 1) (hb : d241830 q = 1) : d281495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32303, d281495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32303, d281495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32304 q = 1) (hb : d241830 q = 1) : d281496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32304, d281496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32304, d281496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro78497 (p : Pattern) (ha : d32404 p = 1) (hb : d241830 p = 1) : d281499 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25766 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32157 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25767 q = 1) (hb : d241830 q = 1) : d25767 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32176 q = 1) (hb : d241830 q = 1) : d281393 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32177 q = 1) (hb : d241830 q = 1) : d281394 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5128 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5128, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5129 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h16 (q : Pattern) (ha : d1565 q = 1) (hb : d241830 q = 1) : d1565 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5130 q = 1) (hb : d241830 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5130, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1578 q = 1) (hb : d241830 q = 1) : d1578 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d5131 q = 1) (hb : d241830 q = 1) : d29787 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d29787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5131, d29787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d5132 q = 1) (hb : d241830 q = 1) : d29788 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d29788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5132, d29788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h21 (q : Pattern) (ha : d32404 q = 1) (hb : d241830 q = 1) : d281499 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32404, d281499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32404, d281499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro78498 (p : Pattern) (ha : d32410 p = 1) (hb : d241830 p = 1) : d281505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d241830 q = 1) : d281405 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78467 q ha hb
    | true =>
      simp only [d32194, d281405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d241830 q = 1) : d281406 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d281406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d241830 q = 1) : d281407 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d281407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d281407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d241830 q = 1) : d281408 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d281408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d281408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d241830 q = 1) : d281410 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78468 q ha hb
    | true =>
      simp only [d32199, d281410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d241830 q = 1) : d281411 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d281411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d241830 q = 1) : d281412 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d281412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d241830 q = 1) : d281413 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d281413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d241830 q = 1) : d281414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d281414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d281414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32405 q = 1) (hb : d241830 q = 1) : d281500 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32405, d281500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78497 q ha hb
    | true =>
      simp only [d32405, d281500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32406 q = 1) (hb : d241830 q = 1) : d281501 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32406, d281501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32406, d281501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32407 q = 1) (hb : d241830 q = 1) : d281502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32407, d281502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32407, d281502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32408 q = 1) (hb : d241830 q = 1) : d281503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32408, d281503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32408, d281503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32409 q = 1) (hb : d241830 q = 1) : d281504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32409, d281504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32409, d281504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32410 q = 1) (hb : d241830 q = 1) : d281505 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32410, d281505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32410, d281505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro78499 (p : Pattern) (ha : d32411 p = 1) (hb : d241830 p = 1) : d281506 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32154 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32155 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32155, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d32156 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25764 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32187 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32188 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32189 q = 1) (hb : d241830 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32189, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32190 q = 1) (hb : d241830 q = 1) : d32190 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32191 q = 1) (hb : d241830 q = 1) : d281402 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32191, d281402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32192 q = 1) (hb : d241830 q = 1) : d281403 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32192, d281403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d5128 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5128, d241830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h17 (q : Pattern) (ha : d5129 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d1565 q = 1) (hb : d241830 q = 1) : d1565 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d5130 q = 1) (hb : d241830 q = 1) : d29564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d5130, d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1578 q = 1) (hb : d241830 q = 1) : d1578 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d5131 q = 1) (hb : d241830 q = 1) : d29787 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d29787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5131, d29787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5132 q = 1) (hb : d241830 q = 1) : d29788 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d29788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5132, d29788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h23 (q : Pattern) (ha : d32411 q = 1) (hb : d241830 q = 1) : d281506 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32411, d281506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32411, d281506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
end NetHack.Soko22Hazard87
