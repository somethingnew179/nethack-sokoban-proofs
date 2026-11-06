import NetHack.Soko22Hazard87.AndIntroBlocks0172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro43250 (p : Pattern) (ha : d173704 p = 1) (hb : d187842 p = 1) : d188449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187837 q = 1) : d188444 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d187837, d188444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43249 q ha hb
    | true =>
      simp only [d187837, d188444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187838 q = 1) : d188445 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d187838, d188445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187838, d188445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187839 q = 1) : d188446 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d187839, d188446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187839, d188446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187840 q = 1) : d188447 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d187840, d188447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187840, d188447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187841 q = 1) : d188448 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d187841, d188448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187841, d188448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187842 q = 1) : d188449 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d187842, d188449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187842, d188449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43251 (p : Pattern) (ha : d173704 p = 1) (hb : d187848 p = 1) : d188455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187843 q = 1) : d188450 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d187843, d188450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43250 q ha hb
    | true =>
      simp only [d187843, d188450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187844 q = 1) : d188451 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d187844, d188451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187844, d188451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187845 q = 1) : d188452 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d187845, d188452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187845, d188452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187846 q = 1) : d188453 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d187846, d188453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187846, d188453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187847 q = 1) : d188454 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d187847, d188454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187847, d188454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187848 q = 1) : d188455 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d187848, d188455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187848, d188455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43252 (p : Pattern) (ha : d173704 p = 1) (hb : d187854 p = 1) : d188461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187849 q = 1) : d188456 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d187849, d188456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43251 q ha hb
    | true =>
      simp only [d187849, d188456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187850 q = 1) : d188457 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d187850, d188457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187850, d188457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187851 q = 1) : d188458 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d187851, d188458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187851, d188458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187852 q = 1) : d188459 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d187852, d188459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187852, d188459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187853 q = 1) : d188460 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d187853, d188460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187853, d188460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187854 q = 1) : d188461 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d187854, d188461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187854, d188461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43253 (p : Pattern) (ha : d173704 p = 1) (hb : d187860 p = 1) : d188467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187855 q = 1) : d188462 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d187855, d188462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43252 q ha hb
    | true =>
      simp only [d187855, d188462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187856 q = 1) : d188463 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d187856, d188463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187856, d188463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187857 q = 1) : d188464 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d187857, d188464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187857, d188464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187858 q = 1) : d188465 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d187858, d188465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187858, d188465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187859 q = 1) : d188466 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d187859, d188466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187859, d188466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187860 q = 1) : d188467 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d187860, d188467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187860, d188467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43254 (p : Pattern) (ha : d173704 p = 1) (hb : d187866 p = 1) : d188473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187861 q = 1) : d188468 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d187861, d188468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43253 q ha hb
    | true =>
      simp only [d187861, d188468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187862 q = 1) : d188469 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d187862, d188469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187862, d188469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187863 q = 1) : d188470 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d187863, d188470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187863, d188470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187864 q = 1) : d188471 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d187864, d188471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187864, d188471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187865 q = 1) : d188472 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d187865, d188472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187865, d188472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187866 q = 1) : d188473 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d187866, d188473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187866, d188473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43255 (p : Pattern) (ha : d173704 p = 1) (hb : d187872 p = 1) : d188479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187867 q = 1) : d188474 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d187867, d188474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43254 q ha hb
    | true =>
      simp only [d187867, d188474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187868 q = 1) : d188475 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d187868, d188475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187868, d188475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187869 q = 1) : d188476 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d187869, d188476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187869, d188476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187870 q = 1) : d188477 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d187870, d188477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187870, d188477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187871 q = 1) : d188478 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d187871, d188478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187871, d188478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187872 q = 1) : d188479 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d187872, d188479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187872, d188479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43256 (p : Pattern) (ha : d173704 p = 1) (hb : d187878 p = 1) : d188485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d173704 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173704 q = 1) (hb : d187873 q = 1) : d188480 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d187873, d188480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43255 q ha hb
    | true =>
      simp only [d187873, d188480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d173704 q = 1) (hb : d187874 q = 1) : d188481 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d187874, d188481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187874, d188481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d173704 q = 1) (hb : d187875 q = 1) : d188482 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d187875, d188482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187875, d188482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d173704 q = 1) (hb : d187876 q = 1) : d188483 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d187876, d188483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187876, d188483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d173704 q = 1) (hb : d187877 q = 1) : d188484 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d187877, d188484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187877, d188484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d173704 q = 1) (hb : d187878 q = 1) : d188485 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d187878, d188485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187878, d188485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43257 (p : Pattern) (ha : d1 p = 1) (hb : d188485 p = 1) : d188485 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d188485 q = 1) : d188485 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro43258 (p : Pattern) (ha : d0 p = 1) (hb : d188485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188485 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro43259 (p : Pattern) (ha : d18548 p = 1) (hb : d131099 p = 1) : d131978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18540 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18541 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18542 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18543 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18547 q = 1) (hb : d131099 q = 1) : d18547 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18548 q = 1) (hb : d131099 q = 1) : d131978 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18548, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18548, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43260 (p : Pattern) (ha : d18554 p = 1) (hb : d131099 p = 1) : d131984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18549 q = 1) (hb : d131099 q = 1) : d131979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43259 q ha hb
    | true =>
      simp only [d18549, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18550 q = 1) (hb : d131099 q = 1) : d131980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18551 q = 1) (hb : d131099 q = 1) : d131981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18551, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18551, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18552 q = 1) (hb : d131099 q = 1) : d131982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18552, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18552, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18553 q = 1) (hb : d131099 q = 1) : d131983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18553, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18553, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18554 q = 1) (hb : d131099 q = 1) : d131984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18554, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18554, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43261 (p : Pattern) (ha : d18560 p = 1) (hb : d131099 p = 1) : d131990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43260 q ha hb
    | true =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18556 q = 1) (hb : d131099 q = 1) : d131986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18556, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18557 q = 1) (hb : d131099 q = 1) : d131987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18557, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18557, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18558 q = 1) (hb : d131099 q = 1) : d131988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18558, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18558, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18559 q = 1) (hb : d131099 q = 1) : d131989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18559, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18559, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18560 q = 1) (hb : d131099 q = 1) : d131990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18560, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18560, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43262 (p : Pattern) (ha : d18566 p = 1) (hb : d131099 p = 1) : d131996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18561 q = 1) (hb : d131099 q = 1) : d131991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18561, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18561, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43261 q ha hb
  have h2 (q : Pattern) (ha : d18562 q = 1) (hb : d131099 q = 1) : d131992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18562, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18562, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18563 q = 1) (hb : d131099 q = 1) : d131993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18563, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18563, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18564 q = 1) (hb : d131099 q = 1) : d131994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18564, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18564, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18565 q = 1) (hb : d131099 q = 1) : d131995 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18565, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18565, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18566 q = 1) (hb : d131099 q = 1) : d131996 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18566, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18566, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43263 (p : Pattern) (ha : d18585 p = 1) (hb : d131099 p = 1) : d132001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18577 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18578 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18539 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18540 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18541 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18579 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18542 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18580 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18584 q = 1) (hb : d131099 q = 1) : d18584 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18585 q = 1) (hb : d131099 q = 1) : d132001 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18585, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18585, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43264 (p : Pattern) (ha : d18591 p = 1) (hb : d131099 p = 1) : d132007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43263 q ha hb
    | true =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18549 q = 1) (hb : d131099 q = 1) : d131979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43259 q ha hb
    | true =>
      simp only [d18549, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18550 q = 1) (hb : d131099 q = 1) : d131980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18588 q = 1) (hb : d131099 q = 1) : d132004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18588, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18588, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18589 q = 1) (hb : d131099 q = 1) : d132005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18589, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18589, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18590 q = 1) (hb : d131099 q = 1) : d132006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18590, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18590, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18591 q = 1) (hb : d131099 q = 1) : d132007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18591, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18591, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43265 (p : Pattern) (ha : d131099 p = 1) (hb : d132592 p = 1) : d132013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d131099 q = 1) : d132008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43264 q ha hb
    | true =>
      simp only [d18592, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43260 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132588 q = 1) : d132009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132588, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132588, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18555 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43260 q ha hb
    | true =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18556 q = 1) (hb : d131099 q = 1) : d131986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18556, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132589 q = 1) : d132010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132589, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132589, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132590 q = 1) : d132011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132590, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132590, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132591 q = 1) : d132012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132591, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132591, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132592 q = 1) : d132013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132592, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132592, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43266 (p : Pattern) (ha : d131099 p = 1) (hb : d132598 p = 1) : d132019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132593 q = 1) : d132014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132593, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132593, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43265 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132594 q = 1) : d132015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132594, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132594, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132595 q = 1) : d132016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132595, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132595, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132596 q = 1) : d132017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132596, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132596, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132597 q = 1) : d132018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132597, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132597, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132598 q = 1) : d132019 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132598, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132598, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43267 (p : Pattern) (ha : d18695 p = 1) (hb : d131099 p = 1) : d132049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d131099 q = 1) : d131985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43260 q ha hb
    | true =>
      simp only [d18555, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18691 q = 1) (hb : d131099 q = 1) : d132045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18691, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18692 q = 1) (hb : d131099 q = 1) : d132046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18692, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18693 q = 1) (hb : d131099 q = 1) : d132047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18693, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18694 q = 1) (hb : d131099 q = 1) : d132048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18694, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18695 q = 1) (hb : d131099 q = 1) : d132049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18695, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43268 (p : Pattern) (ha : d18649 p = 1) (hb : d131099 p = 1) : d132025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18640 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18641 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18642 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18576 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18577 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18578 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18643 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d18539 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d18540 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18540, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18541 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18579 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18644 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18648 q = 1) (hb : d131099 q = 1) : d18648 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d18649 q = 1) (hb : d131099 q = 1) : d132025 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18649, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18649, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43269 (p : Pattern) (ha : d18655 p = 1) (hb : d131099 p = 1) : d132031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18650 q = 1) (hb : d131099 q = 1) : d132026 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18650, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43268 q ha hb
    | true =>
      simp only [d18650, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18651 q = 1) (hb : d131099 q = 1) : d132027 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18651, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18651, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18586 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43263 q ha hb
    | true =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18587 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18652 q = 1) (hb : d131099 q = 1) : d132028 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18652, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18652, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18653 q = 1) (hb : d131099 q = 1) : d132029 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18653, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18653, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18654 q = 1) (hb : d131099 q = 1) : d132030 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18654, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18654, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18655 q = 1) (hb : d131099 q = 1) : d132031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18655, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18655, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43270 (p : Pattern) (ha : d18683 p = 1) (hb : d131099 p = 1) : d132037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d131099 q = 1) : d132002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43263 q ha hb
    | true =>
      simp only [d18586, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d131099 q = 1) : d132003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18680 q = 1) (hb : d131099 q = 1) : d132034 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18680, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18680, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18681 q = 1) (hb : d131099 q = 1) : d132035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18681, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18681, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18682 q = 1) (hb : d131099 q = 1) : d132036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18682, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18682, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18683 q = 1) (hb : d131099 q = 1) : d132037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18683, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18683, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43271 (p : Pattern) (ha : d131099 p = 1) (hb : d132608 p = 1) : d132043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18656 q = 1) (hb : d131099 q = 1) : d132032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18656, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43269 q ha hb
    | true =>
      simp only [d18656, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43264 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132604 q = 1) : d132033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132604, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132604, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18684 q = 1) (hb : d131099 q = 1) : d132038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18684, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43270 q ha hb
    | true =>
      simp only [d18684, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18685 q = 1) (hb : d131099 q = 1) : d132039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18685, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18685, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132605 q = 1) : d132040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132605, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132605, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132606 q = 1) : d132041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132606, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132606, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132607 q = 1) : d132042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132607, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132607, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132608 q = 1) : d132043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132608, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132608, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43272 (p : Pattern) (ha : d131099 p = 1) (hb : d132614 p = 1) : d132055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132609 q = 1) : d132044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132609, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132609, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43271 q ha hb
  have h2 (q : Pattern) (ha : d18696 q = 1) (hb : d131099 q = 1) : d132050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43267 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132610 q = 1) : d132051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132610, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132610, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132611 q = 1) : d132052 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132611, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132611, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132612 q = 1) : d132053 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132612, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132612, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132613 q = 1) : d132054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132613, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132613, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132614 q = 1) : d132055 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132614, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132614, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43273 (p : Pattern) (ha : d131099 p = 1) (hb : d132620 p = 1) : d132061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18567 q = 1) (hb : d131099 q = 1) : d131997 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18567, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18567, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43262 q ha hb
  have h2 (q : Pattern) (ha : d18568 q = 1) (hb : d131099 q = 1) : d131998 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18568, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18568, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18569 q = 1) (hb : d131099 q = 1) : d131999 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18569, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18569, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18570 q = 1) (hb : d131099 q = 1) : d132000 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18570, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18570, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132599 q = 1) : d132020 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132599, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132599, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43266 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132600 q = 1) : d132021 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132600, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132600, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132601 q = 1) : d132022 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132601, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132601, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132602 q = 1) : d132023 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132602, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132602, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131099 q = 1) (hb : d132603 q = 1) : d132024 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132603, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d132603, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131099 q = 1) (hb : d132615 q = 1) : d132056 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132615, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132615, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43272 q ha hb
  have h11 (q : Pattern) (ha : d131099 q = 1) (hb : d132616 q = 1) : d132057 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132616, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132616, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131099 q = 1) (hb : d132617 q = 1) : d132058 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132617, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132617, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d132618 q = 1) : d132059 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132618, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132618, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d132619 q = 1) : d132060 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132619, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132619, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d132620 q = 1) : d132061 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132620, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d132620, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43274 (p : Pattern) (ha : d18751 p = 1) (hb : d131099 p = 1) : d132072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18577 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18578 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18738 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18749 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18750 q = 1) (hb : d131099 q = 1) : d18750 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18751 q = 1) (hb : d131099 q = 1) : d132072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18751, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18751, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43275 (p : Pattern) (ha : d18811 p = 1) (hb : d131099 p = 1) : d132095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18752 q = 1) (hb : d131099 q = 1) : d132073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43274 q ha hb
    | true =>
      simp only [d18752, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18753 q = 1) (hb : d131099 q = 1) : d132074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18808 q = 1) (hb : d131099 q = 1) : d132092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18808, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18808, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18809 q = 1) (hb : d131099 q = 1) : d132093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18809, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18809, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18810 q = 1) (hb : d131099 q = 1) : d132094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18810, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18810, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18811 q = 1) (hb : d131099 q = 1) : d132095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18811, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18811, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43276 (p : Pattern) (ha : d18817 p = 1) (hb : d131099 p = 1) : d132101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18812 q = 1) (hb : d131099 q = 1) : d132096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18812, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43275 q ha hb
    | true =>
      simp only [d18812, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18813 q = 1) (hb : d131099 q = 1) : d132097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18813, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18813, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18814 q = 1) (hb : d131099 q = 1) : d132098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18814, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18814, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18815 q = 1) (hb : d131099 q = 1) : d132099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18815, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18815, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18816 q = 1) (hb : d131099 q = 1) : d132100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18816, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18816, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18817 q = 1) (hb : d131099 q = 1) : d132101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18817, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18817, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43277 (p : Pattern) (ha : d18735 p = 1) (hb : d131099 p = 1) : d132062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18721 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18721, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18721, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18722 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18725 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18725, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18725, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18726 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18727 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d18640 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d18641 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18642 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d18576 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18577 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d18578 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18643 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18728 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18734 q = 1) (hb : d131099 q = 1) : d18734 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18735 q = 1) (hb : d131099 q = 1) : d132062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18735, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18735, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43278 (p : Pattern) (ha : d18742 p = 1) (hb : d131099 p = 1) : d132065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18640 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18641 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18641, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18642 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18576 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18577 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18577, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18578 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18643 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18738 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18739 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18741 q = 1) (hb : d131099 q = 1) : d18741 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18742 q = 1) (hb : d131099 q = 1) : d132065 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18742, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18742, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43279 (p : Pattern) (ha : d18748 p = 1) (hb : d131099 p = 1) : d132071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18736 q = 1) (hb : d131099 q = 1) : d132063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18736, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43277 q ha hb
    | true =>
      simp only [d18736, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18737 q = 1) (hb : d131099 q = 1) : d132064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18737, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18737, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18743 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43278 q ha hb
    | true =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18744 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18745 q = 1) (hb : d131099 q = 1) : d132068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18745, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18745, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18746 q = 1) (hb : d131099 q = 1) : d132069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18746, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18746, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18747 q = 1) (hb : d131099 q = 1) : d132070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18747, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18747, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18748 q = 1) (hb : d131099 q = 1) : d132071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18748, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18748, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43280 (p : Pattern) (ha : d18757 p = 1) (hb : d131099 p = 1) : d132078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43278 q ha hb
    | true =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18752 q = 1) (hb : d131099 q = 1) : d132073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43274 q ha hb
    | true =>
      simp only [d18752, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18753 q = 1) (hb : d131099 q = 1) : d132074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18754 q = 1) (hb : d131099 q = 1) : d132075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18754, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18754, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18755 q = 1) (hb : d131099 q = 1) : d132076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18755, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18755, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18756 q = 1) (hb : d131099 q = 1) : d132077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18756, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18756, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18757 q = 1) (hb : d131099 q = 1) : d132078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18757, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18757, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43281 (p : Pattern) (ha : d18800 p = 1) (hb : d131099 p = 1) : d132084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d131099 q = 1) : d132066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43278 q ha hb
    | true =>
      simp only [d18743, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d131099 q = 1) : d132067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18797 q = 1) (hb : d131099 q = 1) : d132081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18797, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18797, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18798 q = 1) (hb : d131099 q = 1) : d132082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18798, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18798, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18799 q = 1) (hb : d131099 q = 1) : d132083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18799, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18799, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18800 q = 1) (hb : d131099 q = 1) : d132084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18800, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18800, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43282 (p : Pattern) (ha : d131099 p = 1) (hb : d132625 p = 1) : d132090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18758 q = 1) (hb : d131099 q = 1) : d132079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18758, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43279 q ha hb
    | true =>
      simp only [d18758, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43280 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132621 q = 1) : d132080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132621, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132621, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18801 q = 1) (hb : d131099 q = 1) : d132085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18801, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43281 q ha hb
    | true =>
      simp only [d18801, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18802 q = 1) (hb : d131099 q = 1) : d132086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18802, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18802, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132622 q = 1) : d132087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132622, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132622, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132623 q = 1) : d132088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132623, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132623, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132624 q = 1) : d132089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132624, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132624, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132625 q = 1) : d132090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132625, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132625, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43283 (p : Pattern) (ha : d131099 p = 1) (hb : d132631 p = 1) : d132107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132626 q = 1) : d132091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132626, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132626, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43282 q ha hb
  have h2 (q : Pattern) (ha : d18818 q = 1) (hb : d131099 q = 1) : d132102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18818, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18818, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43276 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132627 q = 1) : d132103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132627, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132627, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132628 q = 1) : d132104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132628, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132628, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132629 q = 1) : d132105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132629, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132629, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132630 q = 1) : d132106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132630, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132630, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132631 q = 1) : d132107 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132631, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132631, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43284 (p : Pattern) (ha : d131099 p = 1) (hb : d132637 p = 1) : d132113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132632 q = 1) : d132108 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132632, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132632, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43283 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132633 q = 1) : d132109 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132633, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132633, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132634 q = 1) : d132110 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132634, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132634, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132635 q = 1) : d132111 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132635, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132635, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132636 q = 1) : d132112 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132636, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132636, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132637 q = 1) : d132113 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132637, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132637, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43285 (p : Pattern) (ha : d18895 p = 1) (hb : d131099 p = 1) : d132125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18863 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18864 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18865 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18882 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18893 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18894 q = 1) (hb : d131099 q = 1) : d18894 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18895 q = 1) (hb : d131099 q = 1) : d132125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18895, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18895, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43286 (p : Pattern) (ha : d18970 p = 1) (hb : d131099 p = 1) : d132148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18896 q = 1) (hb : d131099 q = 1) : d132126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43285 q ha hb
    | true =>
      simp only [d18896, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18897 q = 1) (hb : d131099 q = 1) : d132127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18967 q = 1) (hb : d131099 q = 1) : d132145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18967, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18967, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18968 q = 1) (hb : d131099 q = 1) : d132146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18968, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18968, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18969 q = 1) (hb : d131099 q = 1) : d132147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18969, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18969, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18970 q = 1) (hb : d131099 q = 1) : d132148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18970, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18970, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43287 (p : Pattern) (ha : d18976 p = 1) (hb : d131099 p = 1) : d132154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18971 q = 1) (hb : d131099 q = 1) : d132149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18971, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43286 q ha hb
    | true =>
      simp only [d18971, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18972 q = 1) (hb : d131099 q = 1) : d132150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18972, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18972, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18973 q = 1) (hb : d131099 q = 1) : d132151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18973, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18973, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18974 q = 1) (hb : d131099 q = 1) : d132152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18974, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18974, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18975 q = 1) (hb : d131099 q = 1) : d132153 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18975, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18975, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18976 q = 1) (hb : d131099 q = 1) : d132154 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18976, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18976, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43288 (p : Pattern) (ha : d18879 p = 1) (hb : d131099 p = 1) : d132115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18849 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18849, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18849, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18850 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18853 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18854 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18854, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18854, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18855 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18856 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d18859 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d18860 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18860, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18861 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d18863 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18864 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d18865 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18866 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18867 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18878 q = 1) (hb : d131099 q = 1) : d18878 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d18879 q = 1) (hb : d131099 q = 1) : d132115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18879, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18879, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43289 (p : Pattern) (ha : d18886 p = 1) (hb : d131099 p = 1) : d132118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18860 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18860, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d18861 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d18863 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18864 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18864, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d18865 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18866 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18882 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18883 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18885 q = 1) (hb : d131099 q = 1) : d18885 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18886 q = 1) (hb : d131099 q = 1) : d132118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18886, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18886, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43290 (p : Pattern) (ha : d18892 p = 1) (hb : d131099 p = 1) : d132124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18880 q = 1) (hb : d131099 q = 1) : d132116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18880, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43288 q ha hb
    | true =>
      simp only [d18880, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18881 q = 1) (hb : d131099 q = 1) : d132117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18881, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18881, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18887 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43289 q ha hb
    | true =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18888 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18889 q = 1) (hb : d131099 q = 1) : d132121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18889, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18889, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18890 q = 1) (hb : d131099 q = 1) : d132122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18890, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18890, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18891 q = 1) (hb : d131099 q = 1) : d132123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18891, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18891, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18892 q = 1) (hb : d131099 q = 1) : d132124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18892, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18892, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43291 (p : Pattern) (ha : d18901 p = 1) (hb : d131099 p = 1) : d132131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43289 q ha hb
    | true =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18896 q = 1) (hb : d131099 q = 1) : d132126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43285 q ha hb
    | true =>
      simp only [d18896, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18897 q = 1) (hb : d131099 q = 1) : d132127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18898 q = 1) (hb : d131099 q = 1) : d132128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18898, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18898, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18899 q = 1) (hb : d131099 q = 1) : d132129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18899, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18899, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18900 q = 1) (hb : d131099 q = 1) : d132130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18900, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18900, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18901 q = 1) (hb : d131099 q = 1) : d132131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18901, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18901, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43292 (p : Pattern) (ha : d18959 p = 1) (hb : d131099 p = 1) : d132137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d131099 q = 1) : d132119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43289 q ha hb
    | true =>
      simp only [d18887, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d131099 q = 1) : d132120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18956 q = 1) (hb : d131099 q = 1) : d132134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18956, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18956, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18957 q = 1) (hb : d131099 q = 1) : d132135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18957, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18957, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18958 q = 1) (hb : d131099 q = 1) : d132136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18958, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18958, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18959 q = 1) (hb : d131099 q = 1) : d132137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18959, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18959, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43293 (p : Pattern) (ha : d131099 p = 1) (hb : d132643 p = 1) : d132143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18902 q = 1) (hb : d131099 q = 1) : d132132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18902, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43290 q ha hb
    | true =>
      simp only [d18902, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43291 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132639 q = 1) : d132133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132639, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132639, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18960 q = 1) (hb : d131099 q = 1) : d132138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18960, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43292 q ha hb
    | true =>
      simp only [d18960, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18961 q = 1) (hb : d131099 q = 1) : d132139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18961, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18961, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132640 q = 1) : d132140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132640, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132640, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132641 q = 1) : d132141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132641, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132641, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132642 q = 1) : d132142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132642, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132642, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132643 q = 1) : d132143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132643, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132643, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43294 (p : Pattern) (ha : d131099 p = 1) (hb : d132649 p = 1) : d132160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132644 q = 1) : d132144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132644, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132644, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43293 q ha hb
  have h2 (q : Pattern) (ha : d18977 q = 1) (hb : d131099 q = 1) : d132155 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18977, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18977, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43287 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132645 q = 1) : d132156 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132645, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132645, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132646 q = 1) : d132157 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132646, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132646, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132647 q = 1) : d132158 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132647, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132647, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132648 q = 1) : d132159 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132648, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132648, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132649 q = 1) : d132160 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132649, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132649, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43295 (p : Pattern) (ha : d131099 p = 1) (hb : d132655 p = 1) : d132166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132650 q = 1) : d132161 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132650, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132650, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43294 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132651 q = 1) : d132162 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132651, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132651, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132652 q = 1) : d132163 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132652, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132652, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132653 q = 1) : d132164 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132653, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132653, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132654 q = 1) : d132165 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132654, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132654, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132655 q = 1) : d132166 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132655, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132655, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43296 (p : Pattern) (ha : d19092 p = 1) (hb : d131099 p = 1) : d132179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19083 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19084 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19084, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19085 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19086 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19087 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19091 q = 1) (hb : d131099 q = 1) : d19091 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19092 q = 1) (hb : d131099 q = 1) : d132179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19092, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19092, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43297 (p : Pattern) (ha : d19201 p = 1) (hb : d131099 p = 1) : d132205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19093 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43296 q ha hb
    | true =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19094 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19198 q = 1) (hb : d131099 q = 1) : d132202 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19198, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19198, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19199 q = 1) (hb : d131099 q = 1) : d132203 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19199, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19199, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19200 q = 1) (hb : d131099 q = 1) : d132204 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19200, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19200, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19201 q = 1) (hb : d131099 q = 1) : d132205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19201, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19201, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43298 (p : Pattern) (ha : d19207 p = 1) (hb : d131099 p = 1) : d132211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19202 q = 1) (hb : d131099 q = 1) : d132206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19202, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43297 q ha hb
    | true =>
      simp only [d19202, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19203 q = 1) (hb : d131099 q = 1) : d132207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19203, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19203, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19204 q = 1) (hb : d131099 q = 1) : d132208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19204, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19204, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19205 q = 1) (hb : d131099 q = 1) : d132209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19205, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19205, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19206 q = 1) (hb : d131099 q = 1) : d132210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19206, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19206, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19207 q = 1) (hb : d131099 q = 1) : d132211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19207, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19207, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43299 (p : Pattern) (ha : d19067 p = 1) (hb : d131099 p = 1) : d132169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19019 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19019, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19019, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19020 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19027 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19028 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19028, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19028, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19029 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19030 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19039 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19040 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19041 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d19051 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19052 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d19053 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19054 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19055 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19066 q = 1) (hb : d131099 q = 1) : d19066 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d19067 q = 1) (hb : d131099 q = 1) : d132169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19067, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19067, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43300 (p : Pattern) (ha : d19074 p = 1) (hb : d131099 p = 1) : d132172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19040 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19041 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19051 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19052 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19053 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19054 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19070 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19071 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19073 q = 1) (hb : d131099 q = 1) : d19073 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19074 q = 1) (hb : d131099 q = 1) : d132172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19074, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19074, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43301 (p : Pattern) (ha : d19080 p = 1) (hb : d131099 p = 1) : d132178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19068 q = 1) (hb : d131099 q = 1) : d132170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19068, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43299 q ha hb
    | true =>
      simp only [d19068, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19069 q = 1) (hb : d131099 q = 1) : d132171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19069, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19069, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19075 q = 1) (hb : d131099 q = 1) : d132173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43300 q ha hb
    | true =>
      simp only [d19075, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19076 q = 1) (hb : d131099 q = 1) : d132174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19077 q = 1) (hb : d131099 q = 1) : d132175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19077, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19077, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19078 q = 1) (hb : d131099 q = 1) : d132176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19078, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19078, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19079 q = 1) (hb : d131099 q = 1) : d132177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19079, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19079, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19080 q = 1) (hb : d131099 q = 1) : d132178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19080, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19080, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43302 (p : Pattern) (ha : d19098 p = 1) (hb : d131099 p = 1) : d132185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19075 q = 1) (hb : d131099 q = 1) : d132173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43300 q ha hb
    | true =>
      simp only [d19075, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19076 q = 1) (hb : d131099 q = 1) : d132174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43296 q ha hb
    | true =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19095 q = 1) (hb : d131099 q = 1) : d132182 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19095, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19095, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19096 q = 1) (hb : d131099 q = 1) : d132183 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19096, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19096, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19097 q = 1) (hb : d131099 q = 1) : d132184 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19097, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19097, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19098 q = 1) (hb : d131099 q = 1) : d132185 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19098, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19098, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43303 (p : Pattern) (ha : d19184 p = 1) (hb : d131099 p = 1) : d132188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19040 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19041 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19051 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19052 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19053 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19054 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19175 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19176 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19176, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19176, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19177 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19178 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19179 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19183 q = 1) (hb : d131099 q = 1) : d19183 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19184 q = 1) (hb : d131099 q = 1) : d132188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19184, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19184, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43304 (p : Pattern) (ha : d19190 p = 1) (hb : d131099 p = 1) : d132194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19185 q = 1) (hb : d131099 q = 1) : d132189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19185, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43303 q ha hb
    | true =>
      simp only [d19185, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19186 q = 1) (hb : d131099 q = 1) : d132190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19186, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19186, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19187 q = 1) (hb : d131099 q = 1) : d132191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19187, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19187, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19188 q = 1) (hb : d131099 q = 1) : d132192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19188, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19188, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19189 q = 1) (hb : d131099 q = 1) : d132193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19189, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19189, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19190 q = 1) (hb : d131099 q = 1) : d132194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19190, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19190, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43305 (p : Pattern) (ha : d131099 p = 1) (hb : d132662 p = 1) : d132200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19099 q = 1) (hb : d131099 q = 1) : d132186 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19099, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43301 q ha hb
    | true =>
      simp only [d19099, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43302 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132658 q = 1) : d132187 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132658, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132658, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19191 q = 1) (hb : d131099 q = 1) : d132195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19191, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43304 q ha hb
    | true =>
      simp only [d19191, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19192 q = 1) (hb : d131099 q = 1) : d132196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19192, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19192, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132659 q = 1) : d132197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132659, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132659, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132660 q = 1) : d132198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132660, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132660, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132661 q = 1) : d132199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132661, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132661, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132662 q = 1) : d132200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132662, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132662, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43306 (p : Pattern) (ha : d131099 p = 1) (hb : d132668 p = 1) : d132217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132663 q = 1) : d132201 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132663, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132663, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43305 q ha hb
  have h2 (q : Pattern) (ha : d19208 q = 1) (hb : d131099 q = 1) : d132212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19208, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19208, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43298 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132664 q = 1) : d132213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132664, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132664, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132665 q = 1) : d132214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132665, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132665, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132666 q = 1) : d132215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132666, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132666, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132667 q = 1) : d132216 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132667, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132667, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132668 q = 1) : d132217 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132668, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132668, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43307 (p : Pattern) (ha : d131099 p = 1) (hb : d132674 p = 1) : d132223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132669 q = 1) : d132218 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132669, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132669, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43306 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132670 q = 1) : d132219 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132670, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132670, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132671 q = 1) : d132220 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132671, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132671, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132672 q = 1) : d132221 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132672, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132672, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132673 q = 1) : d132222 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132673, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132673, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132674 q = 1) : d132223 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132674, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132674, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43308 (p : Pattern) (ha : d19327 p = 1) (hb : d131099 p = 1) : d132237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19319 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19319, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19320 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19321 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19322 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19326 q = 1) (hb : d131099 q = 1) : d19326 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19327 q = 1) (hb : d131099 q = 1) : d132237 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19327, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19327, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43309 (p : Pattern) (ha : d19439 p = 1) (hb : d131099 p = 1) : d132263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19328 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43308 q ha hb
    | true =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19329 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19436 q = 1) (hb : d131099 q = 1) : d132260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19436, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19436, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19437 q = 1) (hb : d131099 q = 1) : d132261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19437, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19437, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19438 q = 1) (hb : d131099 q = 1) : d132262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19438, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19438, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19439 q = 1) (hb : d131099 q = 1) : d132263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19439, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19439, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43310 (p : Pattern) (ha : d19445 p = 1) (hb : d131099 p = 1) : d132269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19440 q = 1) (hb : d131099 q = 1) : d132264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19440, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43309 q ha hb
    | true =>
      simp only [d19440, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19441 q = 1) (hb : d131099 q = 1) : d132265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19441, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19441, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19442 q = 1) (hb : d131099 q = 1) : d132266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19442, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19442, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19443 q = 1) (hb : d131099 q = 1) : d132267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19443, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19443, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19444 q = 1) (hb : d131099 q = 1) : d132268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19444, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19444, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19445 q = 1) (hb : d131099 q = 1) : d132269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19445, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19445, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43311 (p : Pattern) (ha : d19299 p = 1) (hb : d131099 p = 1) : d132227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19251 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19251, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19251, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19252 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19259 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19260 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19260, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19260, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19261 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19262 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19271 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19272 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19273 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d19283 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19284 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d19285 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19286 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19287 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19298 q = 1) (hb : d131099 q = 1) : d19298 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d19299 q = 1) (hb : d131099 q = 1) : d132227 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19299, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19299, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43312 (p : Pattern) (ha : d19306 p = 1) (hb : d131099 p = 1) : d132230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19271 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19272 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19273 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19283 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19284 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19285 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19286 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19302 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19303 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19305 q = 1) (hb : d131099 q = 1) : d19305 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19306 q = 1) (hb : d131099 q = 1) : d132230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19306, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19306, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43313 (p : Pattern) (ha : d19312 p = 1) (hb : d131099 p = 1) : d132236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19300 q = 1) (hb : d131099 q = 1) : d132228 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19300, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43311 q ha hb
    | true =>
      simp only [d19300, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19301 q = 1) (hb : d131099 q = 1) : d132229 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19301, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19301, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19307 q = 1) (hb : d131099 q = 1) : d132231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43312 q ha hb
    | true =>
      simp only [d19307, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19308 q = 1) (hb : d131099 q = 1) : d132232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19309 q = 1) (hb : d131099 q = 1) : d132233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19309, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19309, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19310 q = 1) (hb : d131099 q = 1) : d132234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19310, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19310, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19311 q = 1) (hb : d131099 q = 1) : d132235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19311, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19311, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19312 q = 1) (hb : d131099 q = 1) : d132236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19312, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19312, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43314 (p : Pattern) (ha : d19333 p = 1) (hb : d131099 p = 1) : d132243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19307 q = 1) (hb : d131099 q = 1) : d132231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43312 q ha hb
    | true =>
      simp only [d19307, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19308 q = 1) (hb : d131099 q = 1) : d132232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43308 q ha hb
    | true =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19330 q = 1) (hb : d131099 q = 1) : d132240 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19330, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19330, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19331 q = 1) (hb : d131099 q = 1) : d132241 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19331, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19331, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19332 q = 1) (hb : d131099 q = 1) : d132242 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19332, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19332, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19333 q = 1) (hb : d131099 q = 1) : d132243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19333, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19333, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43315 (p : Pattern) (ha : d19422 p = 1) (hb : d131099 p = 1) : d132246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19271 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19272 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19273 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19283 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19284 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19285 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19286 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19413 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19414 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19414, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19414, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19415 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19416 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19417 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19421 q = 1) (hb : d131099 q = 1) : d19421 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19422 q = 1) (hb : d131099 q = 1) : d132246 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19422, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19422, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43316 (p : Pattern) (ha : d19428 p = 1) (hb : d131099 p = 1) : d132252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19423 q = 1) (hb : d131099 q = 1) : d132247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19423, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43315 q ha hb
    | true =>
      simp only [d19423, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19424 q = 1) (hb : d131099 q = 1) : d132248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19424, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19424, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19425 q = 1) (hb : d131099 q = 1) : d132249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19425, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19425, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19426 q = 1) (hb : d131099 q = 1) : d132250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19426, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19426, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19427 q = 1) (hb : d131099 q = 1) : d132251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19427, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19427, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19428 q = 1) (hb : d131099 q = 1) : d132252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19428, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19428, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43317 (p : Pattern) (ha : d131099 p = 1) (hb : d132682 p = 1) : d132258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19334 q = 1) (hb : d131099 q = 1) : d132244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19334, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43313 q ha hb
    | true =>
      simp only [d19334, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43314 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132678 q = 1) : d132245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132678, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132678, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19429 q = 1) (hb : d131099 q = 1) : d132253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19429, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43316 q ha hb
    | true =>
      simp only [d19429, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19430 q = 1) (hb : d131099 q = 1) : d132254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19430, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19430, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132679 q = 1) : d132255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132679, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132679, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132680 q = 1) : d132256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132680, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132680, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132681 q = 1) : d132257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132681, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132681, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132682 q = 1) : d132258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132682, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132682, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43318 (p : Pattern) (ha : d131099 p = 1) (hb : d132688 p = 1) : d132275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132683 q = 1) : d132259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132683, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132683, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43317 q ha hb
  have h2 (q : Pattern) (ha : d19446 q = 1) (hb : d131099 q = 1) : d132270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19446, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19446, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43310 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132684 q = 1) : d132271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132684, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132684, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132685 q = 1) : d132272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132685, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132685, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132686 q = 1) : d132273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132686, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132686, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132687 q = 1) : d132274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132687, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132687, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132688 q = 1) : d132275 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132688, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132688, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43319 (p : Pattern) (ha : d131099 p = 1) (hb : d132694 p = 1) : d132281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132689 q = 1) : d132276 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132689, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132689, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43318 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132690 q = 1) : d132277 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132690, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132690, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132691 q = 1) : d132278 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132691, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132691, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132692 q = 1) : d132279 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132692, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132692, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132693 q = 1) : d132280 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132693, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132693, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132694 q = 1) : d132281 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132694, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132694, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43320 (p : Pattern) (ha : d19559 p = 1) (hb : d131099 p = 1) : d132296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19551 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19551, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19552 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19553 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19554 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19558 q = 1) (hb : d131099 q = 1) : d19558 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19559 q = 1) (hb : d131099 q = 1) : d132296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19559, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19559, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43321 (p : Pattern) (ha : d19671 p = 1) (hb : d131099 p = 1) : d132322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19560 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43320 q ha hb
    | true =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19561 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19668 q = 1) (hb : d131099 q = 1) : d132319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19668, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19668, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19669 q = 1) (hb : d131099 q = 1) : d132320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19669, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19669, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19670 q = 1) (hb : d131099 q = 1) : d132321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19670, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19670, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19671 q = 1) (hb : d131099 q = 1) : d132322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19671, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19671, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43322 (p : Pattern) (ha : d19677 p = 1) (hb : d131099 p = 1) : d132328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19672 q = 1) (hb : d131099 q = 1) : d132323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19672, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43321 q ha hb
    | true =>
      simp only [d19672, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19673 q = 1) (hb : d131099 q = 1) : d132324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19673, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19673, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19674 q = 1) (hb : d131099 q = 1) : d132325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19674, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19674, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19675 q = 1) (hb : d131099 q = 1) : d132326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19675, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19675, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19676 q = 1) (hb : d131099 q = 1) : d132327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19676, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19676, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19677 q = 1) (hb : d131099 q = 1) : d132328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19677, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19677, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43323 (p : Pattern) (ha : d19531 p = 1) (hb : d131099 p = 1) : d132286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19486 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19487 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19487, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19487, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19488 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19491 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19492 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19492, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19492, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19493 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19494 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19503 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19504 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19505 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d19515 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19516 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d19517 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19518 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19519 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19530 q = 1) (hb : d131099 q = 1) : d19530 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d19531 q = 1) (hb : d131099 q = 1) : d132286 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19531, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19531, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro43324 (p : Pattern) (ha : d19538 p = 1) (hb : d131099 p = 1) : d132289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19503 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19504 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19505 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19515 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19516 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19517 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19518 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19534 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19535 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19537 q = 1) (hb : d131099 q = 1) : d19537 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19538 q = 1) (hb : d131099 q = 1) : d132289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19538, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19538, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43325 (p : Pattern) (ha : d19544 p = 1) (hb : d131099 p = 1) : d132295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19532 q = 1) (hb : d131099 q = 1) : d132287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19532, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43323 q ha hb
    | true =>
      simp only [d19532, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19533 q = 1) (hb : d131099 q = 1) : d132288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19533, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19533, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19539 q = 1) (hb : d131099 q = 1) : d132290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43324 q ha hb
    | true =>
      simp only [d19539, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19540 q = 1) (hb : d131099 q = 1) : d132291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19541 q = 1) (hb : d131099 q = 1) : d132292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19541, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19541, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19542 q = 1) (hb : d131099 q = 1) : d132293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19542, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19542, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19543 q = 1) (hb : d131099 q = 1) : d132294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19543, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19543, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19544 q = 1) (hb : d131099 q = 1) : d132295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19544, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19544, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43326 (p : Pattern) (ha : d19565 p = 1) (hb : d131099 p = 1) : d132302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19539 q = 1) (hb : d131099 q = 1) : d132290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43324 q ha hb
    | true =>
      simp only [d19539, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19540 q = 1) (hb : d131099 q = 1) : d132291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43320 q ha hb
    | true =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19562 q = 1) (hb : d131099 q = 1) : d132299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19562, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19562, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19563 q = 1) (hb : d131099 q = 1) : d132300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19563, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19563, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19564 q = 1) (hb : d131099 q = 1) : d132301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19564, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19564, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19565 q = 1) (hb : d131099 q = 1) : d132302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19565, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19565, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43327 (p : Pattern) (ha : d19654 p = 1) (hb : d131099 p = 1) : d132305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19503 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19504 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19505 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19515 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19516 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19517 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19518 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19646 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19646, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19646, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19647 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19648 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19649 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19653 q = 1) (hb : d131099 q = 1) : d19653 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d19654 q = 1) (hb : d131099 q = 1) : d132305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19654, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19654, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43328 (p : Pattern) (ha : d19660 p = 1) (hb : d131099 p = 1) : d132311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19655 q = 1) (hb : d131099 q = 1) : d132306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19655, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43327 q ha hb
    | true =>
      simp only [d19655, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19656 q = 1) (hb : d131099 q = 1) : d132307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19656, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19656, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19657 q = 1) (hb : d131099 q = 1) : d132308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19657, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19657, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19658 q = 1) (hb : d131099 q = 1) : d132309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19658, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19658, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19659 q = 1) (hb : d131099 q = 1) : d132310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19659, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19659, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19660 q = 1) (hb : d131099 q = 1) : d132311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19660, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19660, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43329 (p : Pattern) (ha : d131099 p = 1) (hb : d132703 p = 1) : d132317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19566 q = 1) (hb : d131099 q = 1) : d132303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19566, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43325 q ha hb
    | true =>
      simp only [d19566, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43326 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132699 q = 1) : d132304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132699, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132699, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19661 q = 1) (hb : d131099 q = 1) : d132312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19661, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43328 q ha hb
    | true =>
      simp only [d19661, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19662 q = 1) (hb : d131099 q = 1) : d132313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19662, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19662, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132700 q = 1) : d132314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132700, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132700, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132701 q = 1) : d132315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132701, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132701, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132702 q = 1) : d132316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132702, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132702, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132703 q = 1) : d132317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132703, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132703, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43330 (p : Pattern) (ha : d131099 p = 1) (hb : d132709 p = 1) : d132334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132704 q = 1) : d132318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132704, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132704, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43329 q ha hb
  have h2 (q : Pattern) (ha : d19678 q = 1) (hb : d131099 q = 1) : d132329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19678, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19678, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43322 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132705 q = 1) : d132330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132705, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132705, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132706 q = 1) : d132331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132706, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132706, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132707 q = 1) : d132332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132707, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132707, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132708 q = 1) : d132333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132708, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132708, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132709 q = 1) : d132334 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132709, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132709, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43331 (p : Pattern) (ha : d131099 p = 1) (hb : d132715 p = 1) : d132340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132710 q = 1) : d132335 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132710, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132710, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43330 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132711 q = 1) : d132336 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132711, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132711, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132712 q = 1) : d132337 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132712, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132712, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132713 q = 1) : d132338 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132713, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132713, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132714 q = 1) : d132339 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132714, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132714, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132715 q = 1) : d132340 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132715, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132715, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43332 (p : Pattern) (ha : d131099 p = 1) (hb : d132721 p = 1) : d132346 p = 1 := by
  have h0 (q : Pattern) (ha : d131099 q = 1) (hb : d132638 q = 1) : d132114 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132638, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43273 q ha hb
    | true =>
      simp only [d132638, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43284 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132656 q = 1) : d132167 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132656, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132656, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43295 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132657 q = 1) : d132168 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132657, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132657, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132675 q = 1) : d132224 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132675, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132675, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43307 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132676 q = 1) : d132225 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132676, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132676, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132677 q = 1) : d132226 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132677, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132677, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d132695 q = 1) : d132282 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132695, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132695, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43319 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d132696 q = 1) : d132283 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132696, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132696, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131099 q = 1) (hb : d132697 q = 1) : d132284 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132697, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132697, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131099 q = 1) (hb : d132698 q = 1) : d132285 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132698, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132698, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131099 q = 1) (hb : d132716 q = 1) : d132341 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132716, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132716, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43331 q ha hb
  have h12 (q : Pattern) (ha : d131099 q = 1) (hb : d132717 q = 1) : d132342 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132717, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132717, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d132718 q = 1) : d132343 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132718, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132718, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d132719 q = 1) : d132344 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132719, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132719, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d132720 q = 1) : d132345 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132720, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132720, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131099 q = 1) (hb : d132721 q = 1) : d132346 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132721, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132721, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43333 (p : Pattern) (ha : d131099 p = 1) (hb : d132727 p = 1) : d132352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132722 q = 1) : d132347 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132722, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43332 q ha hb
    | true =>
      simp only [d132722, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132723 q = 1) : d132348 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132723, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132723, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132724 q = 1) : d132349 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132724, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132724, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132725 q = 1) : d132350 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132725, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132725, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132726 q = 1) : d132351 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132726, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132726, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132727 q = 1) : d132352 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132727, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132727, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43334 (p : Pattern) (ha : d131099 p = 1) (hb : d132733 p = 1) : d132358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132728 q = 1) : d132353 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132728, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43333 q ha hb
    | true =>
      simp only [d132728, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132729 q = 1) : d132354 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132729, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132729, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132730 q = 1) : d132355 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132730, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132730, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132731 q = 1) : d132356 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132731, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132731, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132732 q = 1) : d132357 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132732, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132732, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132733 q = 1) : d132358 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132733, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132733, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43335 (p : Pattern) (ha : d131099 p = 1) (hb : d132739 p = 1) : d132364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132734 q = 1) : d132359 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132734, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43334 q ha hb
    | true =>
      simp only [d132734, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132735 q = 1) : d132360 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132735, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132735, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132736 q = 1) : d132361 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132736, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132736, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132737 q = 1) : d132362 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132737, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132737, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132738 q = 1) : d132363 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132738, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132738, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132739 q = 1) : d132364 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132739, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132739, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43336 (p : Pattern) (ha : d131099 p = 1) (hb : d132745 p = 1) : d132370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132740 q = 1) : d132365 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132740, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43335 q ha hb
    | true =>
      simp only [d132740, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132741 q = 1) : d132366 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132741, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132741, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132742 q = 1) : d132367 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132742, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132742, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132743 q = 1) : d132368 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132743, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132743, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132744 q = 1) : d132369 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132744, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132744, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132745 q = 1) : d132370 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132745, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132745, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43337 (p : Pattern) (ha : d131099 p = 1) (hb : d132751 p = 1) : d132376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132746 q = 1) : d132371 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132746, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43336 q ha hb
    | true =>
      simp only [d132746, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132747 q = 1) : d132372 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132747, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132747, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132748 q = 1) : d132373 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132748, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132748, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132749 q = 1) : d132374 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132749, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132749, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132750 q = 1) : d132375 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132750, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132750, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132751 q = 1) : d132376 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132751, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132751, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43338 (p : Pattern) (ha : d131099 p = 1) (hb : d132757 p = 1) : d132382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132752 q = 1) : d132377 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132752, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43337 q ha hb
    | true =>
      simp only [d132752, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132753 q = 1) : d132378 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132753, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132753, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132754 q = 1) : d132379 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132754, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132754, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132755 q = 1) : d132380 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132755, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132755, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132756 q = 1) : d132381 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132756, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132756, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132757 q = 1) : d132382 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132757, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132757, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43339 (p : Pattern) (ha : d131099 p = 1) (hb : d132763 p = 1) : d132388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d132758 q = 1) : d132383 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132758, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43338 q ha hb
    | true =>
      simp only [d132758, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d132759 q = 1) : d132384 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132759, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132759, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d132760 q = 1) : d132385 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132760, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132760, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d132761 q = 1) : d132386 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132761, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132761, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d132762 q = 1) : d132387 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132762, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132762, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d132763 q = 1) : d132388 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132763, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132763, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43340 (p : Pattern) (ha : d100953 p = 1) (hb : d131978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18546 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18547 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18547, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18547, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d100953 q = 1) (hb : d131978 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d100953, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100953, d131978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43341 (p : Pattern) (ha : d100959 p = 1) (hb : d131984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100954 q = 1) (hb : d131979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d100954, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43340 q ha hb
    | true =>
      simp only [d100954, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100955 q = 1) (hb : d131980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d100955, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100955, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100956 q = 1) (hb : d131981 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d100956, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100956, d131981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100957 q = 1) (hb : d131982 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d100957, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100957, d131982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100958 q = 1) (hb : d131983 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d100958, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d100958, d131983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100959 q = 1) (hb : d131984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d100959, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d100959, d131984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43342 (p : Pattern) (ha : d100965 p = 1) (hb : d131990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100960 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
    | true =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100961 q = 1) (hb : d131986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100961, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100961, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100962 q = 1) (hb : d131987 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d100962, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100962, d131987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100963 q = 1) (hb : d131988 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d100963, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100963, d131988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100964 q = 1) (hb : d131989 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d100964, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100964, d131989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100965 q = 1) (hb : d131990 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d100965, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100965, d131990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43343 (p : Pattern) (ha : d100971 p = 1) (hb : d131996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100966 q = 1) (hb : d131991 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d100966, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100966, d131991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43342 q ha hb
  have h2 (q : Pattern) (ha : d100967 q = 1) (hb : d131992 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d100967, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100967, d131992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100968 q = 1) (hb : d131993 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d100968, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100968, d131993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100969 q = 1) (hb : d131994 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d100969, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100969, d131994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100970 q = 1) (hb : d131995 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d100970, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d100970, d131995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100971 q = 1) (hb : d131996 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d100971, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100971, d131996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43344 (p : Pattern) (ha : d100986 p = 1) (hb : d132001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h2 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18583 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18546 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18584 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18584, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18584, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d100986 q = 1) (hb : d132001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d100986, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100986, d132001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43345 (p : Pattern) (ha : d100992 p = 1) (hb : d132007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100987 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43344 q ha hb
    | true =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100988 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100954 q = 1) (hb : d131979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d100954, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43340 q ha hb
    | true =>
      simp only [d100954, d131979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100955 q = 1) (hb : d131980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d100955, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100955, d131980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100989 q = 1) (hb : d132004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d100989, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100989, d132004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d100990 q = 1) (hb : d132005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d100990, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d100990, d132005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d100991 q = 1) (hb : d132006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d100991, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d100991, d132006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d100992 q = 1) (hb : d132007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d100992, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d100992, d132007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43346 (p : Pattern) (ha : d100998 p = 1) (hb : d132013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100993 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100993, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43345 q ha hb
    | true =>
      simp only [d100993, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d100960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100994 q = 1) (hb : d132009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100994, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100994, d132009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d100960 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
    | true =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100961 q = 1) (hb : d131986 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100961, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d100961, d131986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100995 q = 1) (hb : d132010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d100995, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100995, d132010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100996 q = 1) (hb : d132011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d100996, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100996, d132011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100997 q = 1) (hb : d132012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d100997, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100997, d132012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100998 q = 1) (hb : d132013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d100998, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100998, d132013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43347 (p : Pattern) (ha : d101004 p = 1) (hb : d132019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100999 q = 1) (hb : d132014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d100999, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100999, d132014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43346 q ha hb
  have h2 (q : Pattern) (ha : d101000 q = 1) (hb : d132015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101000, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101000, d132015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101001 q = 1) (hb : d132016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101001, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101001, d132016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101002 q = 1) (hb : d132017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101002, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101002, d132017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101003 q = 1) (hb : d132018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101003, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101003, d132018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101004 q = 1) (hb : d132019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101004, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101004, d132019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43348 (p : Pattern) (ha : d101027 p = 1) (hb : d132025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h2 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h5 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18583 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18648 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18648, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18648, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101027 q = 1) (hb : d132025 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101027, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101027, d132025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43349 (p : Pattern) (ha : d101033 p = 1) (hb : d132031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101028 q = 1) (hb : d132026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101028, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43348 q ha hb
    | true =>
      simp only [d101028, d132026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101029 q = 1) (hb : d132027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101029, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101029, d132027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100987 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43344 q ha hb
    | true =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100988 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101030 q = 1) (hb : d132028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101030, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101030, d132028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101031 q = 1) (hb : d132029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101031, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101031, d132029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101032 q = 1) (hb : d132030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101032, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101032, d132030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101033 q = 1) (hb : d132031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101033, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101033, d132031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43350 (p : Pattern) (ha : d101039 p = 1) (hb : d132037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100987 q = 1) (hb : d132002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43344 q ha hb
    | true =>
      simp only [d100987, d132002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100988 q = 1) (hb : d132003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100988, d132003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101036 q = 1) (hb : d132034 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101036, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101036, d132034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101037 q = 1) (hb : d132035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101037, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101037, d132035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101038 q = 1) (hb : d132036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101038, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101038, d132036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101039 q = 1) (hb : d132037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101039, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101039, d132037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43351 (p : Pattern) (ha : d101045 p = 1) (hb : d132043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101034 q = 1) (hb : d132032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101034, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43349 q ha hb
    | true =>
      simp only [d101034, d132032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43345 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101035 q = 1) (hb : d132033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101035, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101035, d132033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101040 q = 1) (hb : d132038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101040, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43350 q ha hb
    | true =>
      simp only [d101040, d132038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101041 q = 1) (hb : d132039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101041, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101041, d132039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101042 q = 1) (hb : d132040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101042, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101042, d132040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101043 q = 1) (hb : d132041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101043, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101043, d132041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101044 q = 1) (hb : d132042 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101044, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101044, d132042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101045 q = 1) (hb : d132043 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101045, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101045, d132043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43352 (p : Pattern) (ha : d101051 p = 1) (hb : d132049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100960 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
    | true =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101047 q = 1) (hb : d132045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101047, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101047, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101048 q = 1) (hb : d132046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101048, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101048, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101049 q = 1) (hb : d132047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101049, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101049, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101050 q = 1) (hb : d132048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101050, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101050, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101051 q = 1) (hb : d132049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101051, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101051, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43353 (p : Pattern) (ha : d101057 p = 1) (hb : d132055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101046 q = 1) (hb : d132044 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101046, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101046, d132044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43351 q ha hb
  have h2 (q : Pattern) (ha : d101052 q = 1) (hb : d132050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101052, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101052, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43352 q ha hb
  have h3 (q : Pattern) (ha : d101053 q = 1) (hb : d132051 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101053, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101053, d132051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101054 q = 1) (hb : d132052 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101054, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101054, d132052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101055 q = 1) (hb : d132053 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101055, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101055, d132053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101056 q = 1) (hb : d132054 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101056, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101056, d132054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101057 q = 1) (hb : d132055 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101057, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101057, d132055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43354 (p : Pattern) (ha : d101063 p = 1) (hb : d132061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100972 q = 1) (hb : d131997 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d100972, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100972, d131997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43343 q ha hb
  have h2 (q : Pattern) (ha : d100973 q = 1) (hb : d131998 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d100973, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100973, d131998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100974 q = 1) (hb : d131999 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d100974, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100974, d131999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d100975 q = 1) (hb : d132000 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d100975, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100975, d132000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101005 q = 1) (hb : d132020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101005, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101005, d132020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43347 q ha hb
  have h6 (q : Pattern) (ha : d101006 q = 1) (hb : d132021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101006, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101006, d132021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101007 q = 1) (hb : d132022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101007, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101007, d132022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101008 q = 1) (hb : d132023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101008, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101008, d132023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101009 q = 1) (hb : d132024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101009, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101009, d132024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101058 q = 1) (hb : d132056 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101058, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101058, d132056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43353 q ha hb
  have h11 (q : Pattern) (ha : d101059 q = 1) (hb : d132057 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101059, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101059, d132057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101060 q = 1) (hb : d132058 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101060, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101060, d132058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101061 q = 1) (hb : d132059 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101061, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101061, d132059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101062 q = 1) (hb : d132060 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101062, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101062, d132060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101063 q = 1) (hb : d132061 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101063, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101063, d132061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43355 (p : Pattern) (ha : d101099 p = 1) (hb : d132062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42112 q ha hb
    | true =>
      simp only [d16078, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
  have h2 (q : Pattern) (ha : d18729 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18729, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18729, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18730 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18730, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18730, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d16082, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42113 q ha hb
  have h5 (q : Pattern) (ha : d18731 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18731, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18731, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18732 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18732, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18732, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18733 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18733, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18733, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h9 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h12 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18734 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18734, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18734, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101099 q = 1) (hb : d132062 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101099, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101099, d132062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro43356 (p : Pattern) (ha : d101104 p = 1) (hb : d132065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h2 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h5 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18740 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18741 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18741, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18741, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101104 q = 1) (hb : d132065 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101104, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101104, d132065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43357 (p : Pattern) (ha : d101110 p = 1) (hb : d132071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101100 q = 1) (hb : d132063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101100, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43355 q ha hb
    | true =>
      simp only [d101100, d132063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101101 q = 1) (hb : d132064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101101, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101101, d132064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101105 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43356 q ha hb
    | true =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101106 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101107 q = 1) (hb : d132068 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101107, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101107, d132068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101108 q = 1) (hb : d132069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101108, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101108, d132069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101109 q = 1) (hb : d132070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101109, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101109, d132070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101110 q = 1) (hb : d132071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101110, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101110, d132071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43358 (p : Pattern) (ha : d101112 p = 1) (hb : d132072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h2 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18740 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18750 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18750, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18750, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101112 q = 1) (hb : d132072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101112, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101112, d132072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43359 (p : Pattern) (ha : d101118 p = 1) (hb : d132078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101105 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43356 q ha hb
    | true =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101106 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101113 q = 1) (hb : d132073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101113, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43358 q ha hb
    | true =>
      simp only [d101113, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101114 q = 1) (hb : d132074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101114, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101114, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101115 q = 1) (hb : d132075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101115, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101115, d132075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101116 q = 1) (hb : d132076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101116, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101116, d132076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101117 q = 1) (hb : d132077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101117, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101117, d132077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101118 q = 1) (hb : d132078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101118, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101118, d132078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43360 (p : Pattern) (ha : d101129 p = 1) (hb : d132084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101105 q = 1) (hb : d132066 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43356 q ha hb
    | true =>
      simp only [d101105, d132066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101106 q = 1) (hb : d132067 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101106, d132067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101126 q = 1) (hb : d132081 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101126, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101126, d132081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101127 q = 1) (hb : d132082 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101127, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101127, d132082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101128 q = 1) (hb : d132083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101128, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101128, d132083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101129 q = 1) (hb : d132084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101129, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101129, d132084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43361 (p : Pattern) (ha : d101135 p = 1) (hb : d132090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101119 q = 1) (hb : d132079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101119, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43357 q ha hb
    | true =>
      simp only [d101119, d132079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43359 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101125 q = 1) (hb : d132080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101125, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101125, d132080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101130 q = 1) (hb : d132085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101130, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43360 q ha hb
    | true =>
      simp only [d101130, d132085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101131 q = 1) (hb : d132086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101131, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101131, d132086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101132 q = 1) (hb : d132087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101132, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101132, d132087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101133 q = 1) (hb : d132088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101133, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101133, d132088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101134 q = 1) (hb : d132089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101134, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101134, d132089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101135 q = 1) (hb : d132090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101135, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101135, d132090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43362 (p : Pattern) (ha : d101123 p = 1) (hb : d132095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101113 q = 1) (hb : d132073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101113, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43358 q ha hb
    | true =>
      simp only [d101113, d132073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101114 q = 1) (hb : d132074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101114, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101114, d132074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101120 q = 1) (hb : d132092 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101120, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101120, d132092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101121 q = 1) (hb : d132093 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101121, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101121, d132093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101122 q = 1) (hb : d132094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101122, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101122, d132094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101123 q = 1) (hb : d132095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101123, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101123, d132095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43363 (p : Pattern) (ha : d101142 p = 1) (hb : d132101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101137 q = 1) (hb : d132096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101137, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43362 q ha hb
    | true =>
      simp only [d101137, d132096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101138 q = 1) (hb : d132097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101138, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101138, d132097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101139 q = 1) (hb : d132098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101139, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101139, d132098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101140 q = 1) (hb : d132099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101140, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101140, d132099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101141 q = 1) (hb : d132100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101141, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101141, d132100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101142 q = 1) (hb : d132101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101142, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101142, d132101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43364 (p : Pattern) (ha : d101148 p = 1) (hb : d132107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101136 q = 1) (hb : d132091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101136, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101136, d132091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43361 q ha hb
  have h2 (q : Pattern) (ha : d101143 q = 1) (hb : d132102 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101143, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101143, d132102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43363 q ha hb
  have h3 (q : Pattern) (ha : d101144 q = 1) (hb : d132103 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101144, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101144, d132103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101145 q = 1) (hb : d132104 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101145, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101145, d132104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101146 q = 1) (hb : d132105 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101146, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101146, d132105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101147 q = 1) (hb : d132106 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101147, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101147, d132106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101148 q = 1) (hb : d132107 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101148, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101148, d132107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43365 (p : Pattern) (ha : d101154 p = 1) (hb : d132113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101149 q = 1) (hb : d132108 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101149, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101149, d132108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43364 q ha hb
  have h2 (q : Pattern) (ha : d101150 q = 1) (hb : d132109 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101150, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101150, d132109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101151 q = 1) (hb : d132110 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101151, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101151, d132110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101152 q = 1) (hb : d132111 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101152, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101152, d132111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101153 q = 1) (hb : d132112 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101153, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101153, d132112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101154 q = 1) (hb : d132113 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101154, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101154, d132113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43366 (p : Pattern) (ha : d101209 p = 1) (hb : d132115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42132 q ha hb
    | true =>
      simp only [d16275, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
  have h2 (q : Pattern) (ha : d18868 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18868, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18868, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18869 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18869, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18869, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16279, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42133 q ha hb
  have h5 (q : Pattern) (ha : d18870 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18870, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18870, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18871 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18871, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18871, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18872 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18872, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18872, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
  have h9 (q : Pattern) (ha : d18873 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18874 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h12 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18877 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18878 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18878, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18878, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101209 q = 1) (hb : d132115 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101209, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101209, d132115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro43367 (p : Pattern) (ha : d101214 p = 1) (hb : d132118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
  have h2 (q : Pattern) (ha : d18873 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18874 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h5 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18877 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18884 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18885 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18885, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18885, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101214 q = 1) (hb : d132118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101214, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101214, d132118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43368 (p : Pattern) (ha : d101220 p = 1) (hb : d132124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101210 q = 1) (hb : d132116 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101210, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43366 q ha hb
    | true =>
      simp only [d101210, d132116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101211 q = 1) (hb : d132117 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101211, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101211, d132117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101215 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43367 q ha hb
    | true =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101216 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101217 q = 1) (hb : d132121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101217, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101217, d132121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101218 q = 1) (hb : d132122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101218, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101218, d132122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101219 q = 1) (hb : d132123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101219, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101219, d132123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101220 q = 1) (hb : d132124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101220, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101220, d132124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43369 (p : Pattern) (ha : d101222 p = 1) (hb : d132125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h2 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18884 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18894 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18894, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18894, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101222 q = 1) (hb : d132125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101222, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101222, d132125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43370 (p : Pattern) (ha : d101228 p = 1) (hb : d132131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101215 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43367 q ha hb
    | true =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101216 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101223 q = 1) (hb : d132126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101223, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43369 q ha hb
    | true =>
      simp only [d101223, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101224 q = 1) (hb : d132127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101224, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101224, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101225 q = 1) (hb : d132128 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101225, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101225, d132128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101226 q = 1) (hb : d132129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101226, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101226, d132129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101227 q = 1) (hb : d132130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101227, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101227, d132130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101228 q = 1) (hb : d132131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101228, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101228, d132131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43371 (p : Pattern) (ha : d101239 p = 1) (hb : d132137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101215 q = 1) (hb : d132119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43367 q ha hb
    | true =>
      simp only [d101215, d132119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101216 q = 1) (hb : d132120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101216, d132120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101236 q = 1) (hb : d132134 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101236, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101236, d132134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101237 q = 1) (hb : d132135 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101237, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101237, d132135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101238 q = 1) (hb : d132136 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101238, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101238, d132136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101239 q = 1) (hb : d132137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101239, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101239, d132137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43372 (p : Pattern) (ha : d101245 p = 1) (hb : d132143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101229 q = 1) (hb : d132132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101229, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43368 q ha hb
    | true =>
      simp only [d101229, d132132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43370 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101235 q = 1) (hb : d132133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101235, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101235, d132133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101240 q = 1) (hb : d132138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101240, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43371 q ha hb
    | true =>
      simp only [d101240, d132138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101241 q = 1) (hb : d132139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101241, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101241, d132139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101242 q = 1) (hb : d132140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101242, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101242, d132140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101243 q = 1) (hb : d132141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101243, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101243, d132141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101244 q = 1) (hb : d132142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101244, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101244, d132142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101245 q = 1) (hb : d132143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101245, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101245, d132143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43373 (p : Pattern) (ha : d101233 p = 1) (hb : d132148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101223 q = 1) (hb : d132126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101223, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43369 q ha hb
    | true =>
      simp only [d101223, d132126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101224 q = 1) (hb : d132127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101224, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101224, d132127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101230 q = 1) (hb : d132145 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101230, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101230, d132145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101231 q = 1) (hb : d132146 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101231, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101231, d132146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101232 q = 1) (hb : d132147 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101232, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101232, d132147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101233 q = 1) (hb : d132148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101233, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101233, d132148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43374 (p : Pattern) (ha : d101252 p = 1) (hb : d132154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101247 q = 1) (hb : d132149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101247, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43373 q ha hb
    | true =>
      simp only [d101247, d132149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101248 q = 1) (hb : d132150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101248, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101248, d132150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101249 q = 1) (hb : d132151 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101249, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101249, d132151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101250 q = 1) (hb : d132152 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101250, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101250, d132152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101251 q = 1) (hb : d132153 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101251, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101251, d132153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101252 q = 1) (hb : d132154 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101252, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101252, d132154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43375 (p : Pattern) (ha : d101258 p = 1) (hb : d132160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101246 q = 1) (hb : d132144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101246, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101246, d132144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43372 q ha hb
  have h2 (q : Pattern) (ha : d101253 q = 1) (hb : d132155 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101253, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101253, d132155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43374 q ha hb
  have h3 (q : Pattern) (ha : d101254 q = 1) (hb : d132156 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101254, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101254, d132156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101255 q = 1) (hb : d132157 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101255, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101255, d132157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101256 q = 1) (hb : d132158 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101256, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101256, d132158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101257 q = 1) (hb : d132159 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101257, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101257, d132159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101258 q = 1) (hb : d132160 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101258, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101258, d132160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43376 (p : Pattern) (ha : d101264 p = 1) (hb : d132166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101259 q = 1) (hb : d132161 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101259, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101259, d132161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43375 q ha hb
  have h2 (q : Pattern) (ha : d101260 q = 1) (hb : d132162 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101260, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101260, d132162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101261 q = 1) (hb : d132163 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101261, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101261, d132163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101262 q = 1) (hb : d132164 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101262, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101262, d132164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101263 q = 1) (hb : d132165 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101263, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101263, d132165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101264 q = 1) (hb : d132166 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101264, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101264, d132166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43377 (p : Pattern) (ha : d101377 p = 1) (hb : d132169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42154 q ha hb
    | true =>
      simp only [d16512, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
  have h2 (q : Pattern) (ha : d19056 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19056, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19056, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19057 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19057, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19057, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16517, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42155 q ha hb
  have h5 (q : Pattern) (ha : d19058 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19058, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19058, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19059 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19059, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19059, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19060 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19060, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19060, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h9 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h12 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19066 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19066, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19066, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101377 q = 1) (hb : d132169 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101377, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101377, d132169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro43378 (p : Pattern) (ha : d101382 p = 1) (hb : d132172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h2 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h5 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19072 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19072, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19072, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19073 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19073, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19073, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101382 q = 1) (hb : d132172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101382, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101382, d132172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43379 (p : Pattern) (ha : d101388 p = 1) (hb : d132178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101378 q = 1) (hb : d132170 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101378, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43377 q ha hb
    | true =>
      simp only [d101378, d132170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101379 q = 1) (hb : d132171 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101379, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101379, d132171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101383 q = 1) (hb : d132173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101383, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43378 q ha hb
    | true =>
      simp only [d101383, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101384 q = 1) (hb : d132174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101384, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101384, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101385 q = 1) (hb : d132175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101385, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101385, d132175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101386 q = 1) (hb : d132176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101386, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101386, d132176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101387 q = 1) (hb : d132177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101387, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101387, d132177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101388 q = 1) (hb : d132178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101388, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101388, d132178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43380 (p : Pattern) (ha : d101396 p = 1) (hb : d132179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42145 q ha hb
  have h2 (q : Pattern) (ha : d19088 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19089 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19090 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19091 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19091, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19091, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101396 q = 1) (hb : d132179 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101396, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101396, d132179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43381 (p : Pattern) (ha : d101402 p = 1) (hb : d132185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101383 q = 1) (hb : d132173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101383, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43378 q ha hb
    | true =>
      simp only [d101383, d132173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101384 q = 1) (hb : d132174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101384, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101384, d132174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101397 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43380 q ha hb
    | true =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101398 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101399 q = 1) (hb : d132182 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101399, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101399, d132182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101400 q = 1) (hb : d132183 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101400, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101400, d132183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101401 q = 1) (hb : d132184 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101401, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101401, d132184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101402 q = 1) (hb : d132185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101402, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101402, d132185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43382 (p : Pattern) (ha : d101424 p = 1) (hb : d132188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h2 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h5 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16574, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42164 q ha hb
  have h9 (q : Pattern) (ha : d19180 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19180, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19180, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19181 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19181, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19181, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19182 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19182, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19182, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19183 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19183, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19183, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101424 q = 1) (hb : d132188 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101424, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101424, d132188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43383 (p : Pattern) (ha : d101430 p = 1) (hb : d132194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101425 q = 1) (hb : d132189 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101425, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43382 q ha hb
    | true =>
      simp only [d101425, d132189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101426 q = 1) (hb : d132190 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101426, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101426, d132190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101427 q = 1) (hb : d132191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101427, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101427, d132191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101428 q = 1) (hb : d132192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101428, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101428, d132192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101429 q = 1) (hb : d132193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101429, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101429, d132193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101430 q = 1) (hb : d132194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101430, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101430, d132194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43384 (p : Pattern) (ha : d101436 p = 1) (hb : d132200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101403 q = 1) (hb : d132186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101403, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43379 q ha hb
    | true =>
      simp only [d101403, d132186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43381 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101417 q = 1) (hb : d132187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101417, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101417, d132187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101431 q = 1) (hb : d132195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101431, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43383 q ha hb
    | true =>
      simp only [d101431, d132195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101432 q = 1) (hb : d132196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101432, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101432, d132196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101433 q = 1) (hb : d132197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101433, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101433, d132197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101434 q = 1) (hb : d132198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101434, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101434, d132198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101435 q = 1) (hb : d132199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101435, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101435, d132199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101436 q = 1) (hb : d132200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101436, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101436, d132200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43385 (p : Pattern) (ha : d101415 p = 1) (hb : d132205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101397 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43380 q ha hb
    | true =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101398 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101412 q = 1) (hb : d132202 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101412, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101412, d132202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101413 q = 1) (hb : d132203 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101413, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101413, d132203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101414 q = 1) (hb : d132204 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101414, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101414, d132204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101415 q = 1) (hb : d132205 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101415, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101415, d132205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43386 (p : Pattern) (ha : d101443 p = 1) (hb : d132211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101438 q = 1) (hb : d132206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101438, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43385 q ha hb
    | true =>
      simp only [d101438, d132206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101439 q = 1) (hb : d132207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101439, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101439, d132207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101440 q = 1) (hb : d132208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101440, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101440, d132208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101441 q = 1) (hb : d132209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101441, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101441, d132209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101442 q = 1) (hb : d132210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101442, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101442, d132210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101443 q = 1) (hb : d132211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101443, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101443, d132211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43387 (p : Pattern) (ha : d101449 p = 1) (hb : d132217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101437 q = 1) (hb : d132201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101437, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101437, d132201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43384 q ha hb
  have h2 (q : Pattern) (ha : d101444 q = 1) (hb : d132212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101444, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101444, d132212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43386 q ha hb
  have h3 (q : Pattern) (ha : d101445 q = 1) (hb : d132213 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101445, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101445, d132213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101446 q = 1) (hb : d132214 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101446, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101446, d132214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101447 q = 1) (hb : d132215 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101447, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101447, d132215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101448 q = 1) (hb : d132216 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101448, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101448, d132216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101449 q = 1) (hb : d132217 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101449, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101449, d132217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43388 (p : Pattern) (ha : d101455 p = 1) (hb : d132223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101450 q = 1) (hb : d132218 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101450, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101450, d132218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43387 q ha hb
  have h2 (q : Pattern) (ha : d101451 q = 1) (hb : d132219 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101451, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101451, d132219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101452 q = 1) (hb : d132220 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101452, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101452, d132220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101453 q = 1) (hb : d132221 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101453, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101453, d132221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101454 q = 1) (hb : d132222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101454, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101454, d132222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101455 q = 1) (hb : d132223 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101455, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101455, d132223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43389 (p : Pattern) (ha : d101574 p = 1) (hb : d132227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42180 q ha hb
    | true =>
      simp only [d16864, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
  have h2 (q : Pattern) (ha : d19288 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19288, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19288, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19289 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19289, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19289, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16869, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42181 q ha hb
  have h5 (q : Pattern) (ha : d19290 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19290, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19290, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19291 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19291, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19291, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19292 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19292, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19292, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h9 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h12 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19298 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19298, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19298, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101574 q = 1) (hb : d132227 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101574, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101574, d132227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro43390 (p : Pattern) (ha : d101579 p = 1) (hb : d132230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h2 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h5 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19304 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19304, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19304, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19305 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19305, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19305, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101579 q = 1) (hb : d132230 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101579, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101579, d132230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43391 (p : Pattern) (ha : d101585 p = 1) (hb : d132236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101575 q = 1) (hb : d132228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101575, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43389 q ha hb
    | true =>
      simp only [d101575, d132228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101576 q = 1) (hb : d132229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101576, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101576, d132229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101580 q = 1) (hb : d132231 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101580, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43390 q ha hb
    | true =>
      simp only [d101580, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101581 q = 1) (hb : d132232 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101581, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101581, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101582 q = 1) (hb : d132233 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101582, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101582, d132233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101583 q = 1) (hb : d132234 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101583, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101583, d132234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101584 q = 1) (hb : d132235 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101584, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101584, d132235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101585 q = 1) (hb : d132236 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101585, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101585, d132236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43392 (p : Pattern) (ha : d101596 p = 1) (hb : d132237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42171 q ha hb
  have h2 (q : Pattern) (ha : d19323 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19324 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19325 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19326 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19326, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19326, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101596 q = 1) (hb : d132237 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101596, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101596, d132237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43393 (p : Pattern) (ha : d101602 p = 1) (hb : d132243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101580 q = 1) (hb : d132231 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101580, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43390 q ha hb
    | true =>
      simp only [d101580, d132231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101581 q = 1) (hb : d132232 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101581, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101581, d132232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101597 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43392 q ha hb
    | true =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101598 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101599 q = 1) (hb : d132240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101599, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101599, d132240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101600 q = 1) (hb : d132241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101600, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101600, d132241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101601 q = 1) (hb : d132242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101601, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101601, d132242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101602 q = 1) (hb : d132243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101602, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101602, d132243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43394 (p : Pattern) (ha : d101624 p = 1) (hb : d132246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h2 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h5 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16929 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16929, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42190 q ha hb
  have h9 (q : Pattern) (ha : d19418 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19418, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19418, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19419 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19419, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19419, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19420 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19420, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19420, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19421 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19421, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19421, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101624 q = 1) (hb : d132246 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101624, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101624, d132246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43395 (p : Pattern) (ha : d101630 p = 1) (hb : d132252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101625 q = 1) (hb : d132247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101625, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43394 q ha hb
    | true =>
      simp only [d101625, d132247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101626 q = 1) (hb : d132248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101626, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101626, d132248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101627 q = 1) (hb : d132249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101627, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101627, d132249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101628 q = 1) (hb : d132250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101628, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101628, d132250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101629 q = 1) (hb : d132251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101629, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101629, d132251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101630 q = 1) (hb : d132252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101630, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101630, d132252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43396 (p : Pattern) (ha : d101636 p = 1) (hb : d132258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101603 q = 1) (hb : d132244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101603, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43391 q ha hb
    | true =>
      simp only [d101603, d132244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43393 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101617 q = 1) (hb : d132245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101617, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101617, d132245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101631 q = 1) (hb : d132253 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101631, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43395 q ha hb
    | true =>
      simp only [d101631, d132253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101632 q = 1) (hb : d132254 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101632, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101632, d132254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101633 q = 1) (hb : d132255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101633, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101633, d132255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101634 q = 1) (hb : d132256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101634, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101634, d132256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101635 q = 1) (hb : d132257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101635, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101635, d132257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101636 q = 1) (hb : d132258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101636, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101636, d132258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43397 (p : Pattern) (ha : d101615 p = 1) (hb : d132263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101597 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43392 q ha hb
    | true =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101598 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101612 q = 1) (hb : d132260 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101612, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101612, d132260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101613 q = 1) (hb : d132261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101613, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101613, d132261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101614 q = 1) (hb : d132262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101614, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101614, d132262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101615 q = 1) (hb : d132263 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101615, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101615, d132263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43398 (p : Pattern) (ha : d101643 p = 1) (hb : d132269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101638 q = 1) (hb : d132264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101638, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43397 q ha hb
    | true =>
      simp only [d101638, d132264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101639 q = 1) (hb : d132265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101639, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101639, d132265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101640 q = 1) (hb : d132266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101640, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101640, d132266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101641 q = 1) (hb : d132267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101641, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101641, d132267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101642 q = 1) (hb : d132268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101642, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101642, d132268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101643 q = 1) (hb : d132269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101643, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101643, d132269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43399 (p : Pattern) (ha : d101649 p = 1) (hb : d132275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101637 q = 1) (hb : d132259 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101637, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101637, d132259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43396 q ha hb
  have h2 (q : Pattern) (ha : d101644 q = 1) (hb : d132270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101644, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101644, d132270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43398 q ha hb
  have h3 (q : Pattern) (ha : d101645 q = 1) (hb : d132271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101645, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101645, d132271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101646 q = 1) (hb : d132272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101646, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101646, d132272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101647 q = 1) (hb : d132273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101647, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101647, d132273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101648 q = 1) (hb : d132274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101648, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101648, d132274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101649 q = 1) (hb : d132275 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101649, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101649, d132275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43400 (p : Pattern) (ha : d101655 p = 1) (hb : d132281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101650 q = 1) (hb : d132276 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101650, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101650, d132276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43399 q ha hb
  have h2 (q : Pattern) (ha : d101651 q = 1) (hb : d132277 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101651, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101651, d132277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101652 q = 1) (hb : d132278 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101652, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101652, d132278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101653 q = 1) (hb : d132279 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101653, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101653, d132279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101654 q = 1) (hb : d132280 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101654, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101654, d132280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101655 q = 1) (hb : d132281 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101655, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101655, d132281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43401 (p : Pattern) (ha : d101745 p = 1) (hb : d132286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42206 q ha hb
    | true =>
      simp only [d17230, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
  have h2 (q : Pattern) (ha : d19520 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19520, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19520, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19521 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19521, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19521, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17234, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42207 q ha hb
  have h5 (q : Pattern) (ha : d19522 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19522, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19522, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19523 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19523, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19523, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19524 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19524, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19524, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h9 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h12 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19530 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19530, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19530, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101745 q = 1) (hb : d132286 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101745, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101745, d132286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro43402 (p : Pattern) (ha : d101750 p = 1) (hb : d132289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h2 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h5 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19536 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19536, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19536, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19537 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19537, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19537, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101750 q = 1) (hb : d132289 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101750, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101750, d132289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro43403 (p : Pattern) (ha : d101756 p = 1) (hb : d132295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101746 q = 1) (hb : d132287 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101746, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43401 q ha hb
    | true =>
      simp only [d101746, d132287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101747 q = 1) (hb : d132288 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101747, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101747, d132288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101751 q = 1) (hb : d132290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101751, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43402 q ha hb
    | true =>
      simp only [d101751, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101752 q = 1) (hb : d132291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101752, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101752, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101753 q = 1) (hb : d132292 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101753, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101753, d132292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101754 q = 1) (hb : d132293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101754, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101754, d132293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101755 q = 1) (hb : d132294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101755, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101755, d132294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101756 q = 1) (hb : d132295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101756, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101756, d132295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43404 (p : Pattern) (ha : d101767 p = 1) (hb : d132296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42197 q ha hb
  have h2 (q : Pattern) (ha : d19555 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19556 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19557 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19558 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19558, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19558, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101767 q = 1) (hb : d132296 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101767, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101767, d132296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro43405 (p : Pattern) (ha : d101773 p = 1) (hb : d132302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101751 q = 1) (hb : d132290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101751, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43402 q ha hb
    | true =>
      simp only [d101751, d132290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101752 q = 1) (hb : d132291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101752, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101752, d132291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101768 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43404 q ha hb
    | true =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101769 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101770 q = 1) (hb : d132299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101770, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101770, d132299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101771 q = 1) (hb : d132300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101771, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101771, d132300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101772 q = 1) (hb : d132301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101772, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101772, d132301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101773 q = 1) (hb : d132302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101773, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101773, d132302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43406 (p : Pattern) (ha : d101795 p = 1) (hb : d132305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h2 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h5 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17294 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17294, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42216 q ha hb
  have h9 (q : Pattern) (ha : d19650 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19650, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19650, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19651 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19651, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19651, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19652 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19652, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19652, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19653 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19653, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19653, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101795 q = 1) (hb : d132305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101795, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101795, d132305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43407 (p : Pattern) (ha : d101801 p = 1) (hb : d132311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101796 q = 1) (hb : d132306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101796, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43406 q ha hb
    | true =>
      simp only [d101796, d132306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101797 q = 1) (hb : d132307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101797, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101797, d132307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101798 q = 1) (hb : d132308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101798, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101798, d132308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101799 q = 1) (hb : d132309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101799, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101799, d132309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101800 q = 1) (hb : d132310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101800, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101800, d132310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101801 q = 1) (hb : d132311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101801, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101801, d132311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43408 (p : Pattern) (ha : d101807 p = 1) (hb : d132317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101774 q = 1) (hb : d132303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101774, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43403 q ha hb
    | true =>
      simp only [d101774, d132303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43405 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101787 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101788 q = 1) (hb : d132304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101788, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101788, d132304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101802 q = 1) (hb : d132312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101802, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43407 q ha hb
    | true =>
      simp only [d101802, d132312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101803 q = 1) (hb : d132313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101803, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101803, d132313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101804 q = 1) (hb : d132314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101804, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101804, d132314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101805 q = 1) (hb : d132315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101805, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101805, d132315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101806 q = 1) (hb : d132316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101806, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101806, d132316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101807 q = 1) (hb : d132317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101807, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101807, d132317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43409 (p : Pattern) (ha : d101786 p = 1) (hb : d132322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101768 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43404 q ha hb
    | true =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101769 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101783 q = 1) (hb : d132319 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101783, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101783, d132319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101784 q = 1) (hb : d132320 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101784, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101784, d132320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101785 q = 1) (hb : d132321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101785, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101785, d132321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101786 q = 1) (hb : d132322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101786, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101786, d132322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43410 (p : Pattern) (ha : d101814 p = 1) (hb : d132328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101809 q = 1) (hb : d132323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101809, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43409 q ha hb
    | true =>
      simp only [d101809, d132323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101810 q = 1) (hb : d132324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101810, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101810, d132324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101811 q = 1) (hb : d132325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101811, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101811, d132325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101812 q = 1) (hb : d132326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101812, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101812, d132326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101813 q = 1) (hb : d132327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101813, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101813, d132327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101814 q = 1) (hb : d132328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101814, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101814, d132328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43411 (p : Pattern) (ha : d101820 p = 1) (hb : d132334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101808 q = 1) (hb : d132318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101808, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101808, d132318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43408 q ha hb
  have h2 (q : Pattern) (ha : d101815 q = 1) (hb : d132329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101815, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101815, d132329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43410 q ha hb
  have h3 (q : Pattern) (ha : d101816 q = 1) (hb : d132330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101816, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101816, d132330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101817 q = 1) (hb : d132331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101817, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101817, d132331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101818 q = 1) (hb : d132332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101818, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101818, d132332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101819 q = 1) (hb : d132333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101819, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101819, d132333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101820 q = 1) (hb : d132334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101820, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101820, d132334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43412 (p : Pattern) (ha : d101826 p = 1) (hb : d132340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101821 q = 1) (hb : d132335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101821, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101821, d132335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43411 q ha hb
  have h2 (q : Pattern) (ha : d101822 q = 1) (hb : d132336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101822, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101822, d132336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101823 q = 1) (hb : d132337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101823, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101823, d132337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101824 q = 1) (hb : d132338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101824, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101824, d132338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101825 q = 1) (hb : d132339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101825, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101825, d132339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101826 q = 1) (hb : d132340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101826, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101826, d132340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43413 (p : Pattern) (ha : d101832 p = 1) (hb : d132346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101155 q = 1) (hb : d132114 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101155, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43354 q ha hb
    | true =>
      simp only [d101155, d132114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43365 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101265 q = 1) (hb : d132167 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101265, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101265, d132167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43376 q ha hb
  have h3 (q : Pattern) (ha : d101266 q = 1) (hb : d132168 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101266, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101266, d132168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101456 q = 1) (hb : d132224 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101456, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101456, d132224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43388 q ha hb
  have h5 (q : Pattern) (ha : d101457 q = 1) (hb : d132225 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101457, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101457, d132225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101458 q = 1) (hb : d132226 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101458, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101458, d132226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101656 q = 1) (hb : d132282 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101656, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101656, d132282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43400 q ha hb
  have h8 (q : Pattern) (ha : d101657 q = 1) (hb : d132283 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101657, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101657, d132283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101658 q = 1) (hb : d132284 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101658, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101658, d132284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101659 q = 1) (hb : d132285 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101659, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101659, d132285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101827 q = 1) (hb : d132341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101827, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101827, d132341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43412 q ha hb
  have h12 (q : Pattern) (ha : d101828 q = 1) (hb : d132342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101828, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101828, d132342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101829 q = 1) (hb : d132343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101829, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101829, d132343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101830 q = 1) (hb : d132344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101830, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101830, d132344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101831 q = 1) (hb : d132345 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d101831, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d101831, d132345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101832 q = 1) (hb : d132346 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d101832, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d101832, d132346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43414 (p : Pattern) (ha : d101838 p = 1) (hb : d132352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101833 q = 1) (hb : d132347 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d101833, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43413 q ha hb
    | true =>
      simp only [d101833, d132347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101834 q = 1) (hb : d132348 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d101834, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101834, d132348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101835 q = 1) (hb : d132349 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d101835, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101835, d132349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101836 q = 1) (hb : d132350 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d101836, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101836, d132350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101837 q = 1) (hb : d132351 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d101837, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101837, d132351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101838 q = 1) (hb : d132352 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d101838, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101838, d132352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43415 (p : Pattern) (ha : d101844 p = 1) (hb : d132358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101839 q = 1) (hb : d132353 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d101839, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43414 q ha hb
    | true =>
      simp only [d101839, d132353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101840 q = 1) (hb : d132354 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d101840, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101840, d132354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101841 q = 1) (hb : d132355 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d101841, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101841, d132355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101842 q = 1) (hb : d132356 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d101842, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101842, d132356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101843 q = 1) (hb : d132357 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d101843, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101843, d132357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101844 q = 1) (hb : d132358 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d101844, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101844, d132358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43416 (p : Pattern) (ha : d101850 p = 1) (hb : d132364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101845 q = 1) (hb : d132359 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d101845, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43415 q ha hb
    | true =>
      simp only [d101845, d132359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101846 q = 1) (hb : d132360 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d101846, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101846, d132360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101847 q = 1) (hb : d132361 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d101847, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101847, d132361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101848 q = 1) (hb : d132362 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d101848, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101848, d132362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101849 q = 1) (hb : d132363 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d101849, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101849, d132363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101850 q = 1) (hb : d132364 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d101850, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101850, d132364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43417 (p : Pattern) (ha : d101856 p = 1) (hb : d132370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101851 q = 1) (hb : d132365 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d101851, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43416 q ha hb
    | true =>
      simp only [d101851, d132365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101852 q = 1) (hb : d132366 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d101852, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101852, d132366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101853 q = 1) (hb : d132367 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d101853, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101853, d132367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101854 q = 1) (hb : d132368 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d101854, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101854, d132368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101855 q = 1) (hb : d132369 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d101855, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101855, d132369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101856 q = 1) (hb : d132370 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d101856, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101856, d132370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43418 (p : Pattern) (ha : d101862 p = 1) (hb : d132376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101857 q = 1) (hb : d132371 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d101857, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43417 q ha hb
    | true =>
      simp only [d101857, d132371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101858 q = 1) (hb : d132372 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d101858, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101858, d132372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101859 q = 1) (hb : d132373 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d101859, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101859, d132373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101860 q = 1) (hb : d132374 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d101860, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101860, d132374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101861 q = 1) (hb : d132375 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d101861, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101861, d132375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101862 q = 1) (hb : d132376 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d101862, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101862, d132376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43419 (p : Pattern) (ha : d101868 p = 1) (hb : d132382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101863 q = 1) (hb : d132377 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d101863, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43418 q ha hb
    | true =>
      simp only [d101863, d132377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101864 q = 1) (hb : d132378 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d101864, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101864, d132378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101865 q = 1) (hb : d132379 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d101865, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101865, d132379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101866 q = 1) (hb : d132380 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d101866, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101866, d132380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101867 q = 1) (hb : d132381 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d101867, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101867, d132381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101868 q = 1) (hb : d132382 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d101868, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101868, d132382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43420 (p : Pattern) (ha : d101874 p = 1) (hb : d132388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101869 q = 1) (hb : d132383 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d101869, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43419 q ha hb
    | true =>
      simp only [d101869, d132383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101870 q = 1) (hb : d132384 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d101870, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101870, d132384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101871 q = 1) (hb : d132385 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d101871, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101871, d132385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101872 q = 1) (hb : d132386 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d101872, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101872, d132386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101873 q = 1) (hb : d132387 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d101873, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101873, d132387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101874 q = 1) (hb : d132388 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d101874, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101874, d132388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43421 (p : Pattern) (ha : d131099 p = 1) (hb : d187684 p = 1) : d132393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18696 q = 1) (hb : d131099 q = 1) : d132050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43267 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187680 q = 1) : d132389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187680, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187680, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187681 q = 1) : d132390 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187681, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187681, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187682 q = 1) : d132391 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187682, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187682, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187683 q = 1) : d132392 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187683, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187683, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187684 q = 1) : d132393 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187684, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187684, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43422 (p : Pattern) (ha : d131099 p = 1) (hb : d187694 p = 1) : d132403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d131099 q = 1) : d132008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43264 q ha hb
    | true =>
      simp only [d18592, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43260 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187690 q = 1) : d132399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187690, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187690, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187691 q = 1) : d132400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187691, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187691, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187692 q = 1) : d132401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187692, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187692, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187693 q = 1) : d132402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187693, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187693, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187694 q = 1) : d132403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187694, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187694, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43423 (p : Pattern) (ha : d131099 p = 1) (hb : d187700 p = 1) : d132409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187695 q = 1) : d132404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187695, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187695, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43422 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187696 q = 1) : d132405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187696, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187696, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187697 q = 1) : d132406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187697, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187697, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187698 q = 1) : d132407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187698, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187698, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187699 q = 1) : d132408 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187699, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187699, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187700 q = 1) : d132409 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187700, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187700, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43424 (p : Pattern) (ha : d131099 p = 1) (hb : d187706 p = 1) : d132415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187685 q = 1) : d132394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187685, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187685, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43421 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187686 q = 1) : d132395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187686, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187686, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187687 q = 1) : d132396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187687, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187687, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187688 q = 1) : d132397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187688, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187688, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187689 q = 1) : d132398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187689, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187689, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187701 q = 1) : d132410 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187701, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187701, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43423 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d187702 q = 1) : d132411 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187702, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187702, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d187703 q = 1) : d132412 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187703, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187703, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131099 q = 1) (hb : d187704 q = 1) : d132413 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187704, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187704, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131099 q = 1) (hb : d187705 q = 1) : d132414 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187705, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187705, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131099 q = 1) (hb : d187706 q = 1) : d132415 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187706, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187706, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43425 (p : Pattern) (ha : d131099 p = 1) (hb : d187712 p = 1) : d132421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187707 q = 1) : d132416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187707, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43280 q hb ha
    | true =>
      simp only [d187707, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43275 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187708 q = 1) : d132417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187708, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187708, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187709 q = 1) : d132418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187709, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187709, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187710 q = 1) : d132419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187710, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187710, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187711 q = 1) : d132420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187711, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187711, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187712 q = 1) : d132421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187712, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187712, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43426 (p : Pattern) (ha : d131099 p = 1) (hb : d187718 p = 1) : d132427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187713 q = 1) : d132422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187713, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187713, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43425 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187714 q = 1) : d132423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187714, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187714, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187715 q = 1) : d132424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187715, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187715, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187716 q = 1) : d132425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187716, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187716, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187717 q = 1) : d132426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187717, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187717, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187718 q = 1) : d132427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187718, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187718, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43427 (p : Pattern) (ha : d131099 p = 1) (hb : d187724 p = 1) : d132433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187719 q = 1) : d132428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187719, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187719, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43426 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187720 q = 1) : d132429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187720, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187720, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187721 q = 1) : d132430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187721, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187721, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187722 q = 1) : d132431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187722, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187722, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187723 q = 1) : d132432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187723, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187723, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187724 q = 1) : d132433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187724, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187724, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43428 (p : Pattern) (ha : d131099 p = 1) (hb : d187731 p = 1) : d132440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187726 q = 1) : d132435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187726, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43291 q hb ha
    | true =>
      simp only [d187726, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43286 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187727 q = 1) : d132436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187727, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187727, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187728 q = 1) : d132437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187728, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187728, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187729 q = 1) : d132438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187729, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187729, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187730 q = 1) : d132439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187730, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187730, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187731 q = 1) : d132440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187731, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187731, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43429 (p : Pattern) (ha : d131099 p = 1) (hb : d187737 p = 1) : d132446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187732 q = 1) : d132441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187732, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187732, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43428 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187733 q = 1) : d132442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187733, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187733, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187734 q = 1) : d132443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187734, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187734, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187735 q = 1) : d132444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187735, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187735, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187736 q = 1) : d132445 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187736, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187736, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187737 q = 1) : d132446 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187737, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187737, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43430 (p : Pattern) (ha : d131099 p = 1) (hb : d187743 p = 1) : d132452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187738 q = 1) : d132447 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187738, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187738, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43429 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187739 q = 1) : d132448 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187739, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187739, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187740 q = 1) : d132449 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187740, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187740, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187741 q = 1) : d132450 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187741, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187741, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187742 q = 1) : d132451 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187742, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187742, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187743 q = 1) : d132452 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187743, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187743, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43431 (p : Pattern) (ha : d131099 p = 1) (hb : d187747 p = 1) : d132456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19040 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19040, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19041 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19051 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19052 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19052, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19053 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19054 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19083 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19084 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19084, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19085 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19086 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d187746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d187746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d132455 q = 1) : d132455 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d187747 q = 1) : d132456 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187747, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d187747, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43432 (p : Pattern) (ha : d131099 p = 1) (hb : d187753 p = 1) : d132462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187748 q = 1) : d132457 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187748, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43431 q ha hb
    | true =>
      simp only [d187748, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187749 q = 1) : d132458 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187749, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187749, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d131099 q = 1) : d132180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43296 q ha hb
    | true =>
      simp only [d19093, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d131099 q = 1) : d132181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187750 q = 1) : d132459 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187750, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187750, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187751 q = 1) : d132460 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187751, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187751, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d187752 q = 1) : d132461 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187752, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187752, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d187753 q = 1) : d132462 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187753, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187753, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43433 (p : Pattern) (ha : d131099 p = 1) (hb : d187759 p = 1) : d132468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187754 q = 1) : d132463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187754, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43432 q ha hb
    | true =>
      simp only [d187754, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43297 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187755 q = 1) : d132464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187755, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187755, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187756 q = 1) : d132465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187756, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187756, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187757 q = 1) : d132466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187757, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187757, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187758 q = 1) : d132467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187758, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187758, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187759 q = 1) : d132468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187759, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187759, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43434 (p : Pattern) (ha : d131099 p = 1) (hb : d187765 p = 1) : d132474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187760 q = 1) : d132469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187760, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187760, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43433 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187761 q = 1) : d132470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187761, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187761, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187762 q = 1) : d132471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187762, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187762, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187763 q = 1) : d132472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187763, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187763, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187764 q = 1) : d132473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187764, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187764, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187765 q = 1) : d132474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187765, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187765, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43435 (p : Pattern) (ha : d131099 p = 1) (hb : d187771 p = 1) : d132480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187766 q = 1) : d132475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187766, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187766, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43434 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187767 q = 1) : d132476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187767, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187767, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187768 q = 1) : d132477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187768, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187768, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187769 q = 1) : d132478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187769, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187769, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187770 q = 1) : d132479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187770, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187770, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187771 q = 1) : d132480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187771, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187771, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43436 (p : Pattern) (ha : d131099 p = 1) (hb : d187776 p = 1) : d132485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19271 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19272 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19272, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19273 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19283 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19284 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19284, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19285 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19286 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19318 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19319 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19319, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19320 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19321 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d187775 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d187775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d132484 q = 1) : d132484 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d187776 q = 1) : d132485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187776, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d187776, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43437 (p : Pattern) (ha : d131099 p = 1) (hb : d187782 p = 1) : d132491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187777 q = 1) : d132486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187777, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43436 q ha hb
    | true =>
      simp only [d187777, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187778 q = 1) : d132487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187778, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187778, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d131099 q = 1) : d132238 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43308 q ha hb
    | true =>
      simp only [d19328, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d131099 q = 1) : d132239 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187779 q = 1) : d132488 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187779, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187779, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187780 q = 1) : d132489 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187780, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187780, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d187781 q = 1) : d132490 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187781, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187781, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d187782 q = 1) : d132491 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187782, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187782, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43438 (p : Pattern) (ha : d131099 p = 1) (hb : d187788 p = 1) : d132497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187783 q = 1) : d132492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187783, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43437 q ha hb
    | true =>
      simp only [d187783, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43309 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187784 q = 1) : d132493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187784, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187784, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187785 q = 1) : d132494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187785, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187785, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187786 q = 1) : d132495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187786, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187786, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187787 q = 1) : d132496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187787, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187787, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187788 q = 1) : d132497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187788, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187788, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43439 (p : Pattern) (ha : d131099 p = 1) (hb : d187794 p = 1) : d132503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187789 q = 1) : d132498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187789, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187789, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43438 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187790 q = 1) : d132499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187790, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187790, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187791 q = 1) : d132500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187791, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187791, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187792 q = 1) : d132501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187792, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187792, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187793 q = 1) : d132502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187793, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187793, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187794 q = 1) : d132503 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187794, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187794, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43440 (p : Pattern) (ha : d131099 p = 1) (hb : d187800 p = 1) : d132509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187795 q = 1) : d132504 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187795, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187795, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43439 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187796 q = 1) : d132505 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187796, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187796, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187797 q = 1) : d132506 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187797, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187797, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187798 q = 1) : d132507 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187798, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187798, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187799 q = 1) : d132508 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187799, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187799, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187800 q = 1) : d132509 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187800, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187800, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43441 (p : Pattern) (ha : d131099 p = 1) (hb : d187806 p = 1) : d132515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19503 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19504 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19504, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19505 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d19515 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19516 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19516, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d19517 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19518 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d19550 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19551 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19551, d131099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19552 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19553 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d187805 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d187805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d132514 q = 1) : d132514 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d187806 q = 1) : d132515 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187806, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d187806, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43442 (p : Pattern) (ha : d131099 p = 1) (hb : d187812 p = 1) : d132521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187807 q = 1) : d132516 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187807, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43441 q ha hb
    | true =>
      simp only [d187807, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187808 q = 1) : d132517 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187808, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187808, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d131099 q = 1) : d132297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43320 q ha hb
    | true =>
      simp only [d19560, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d131099 q = 1) : d132298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187809 q = 1) : d132518 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187809, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187809, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187810 q = 1) : d132519 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187810, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187810, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d187811 q = 1) : d132520 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187811, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187811, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d187812 q = 1) : d132521 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187812, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187812, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43443 (p : Pattern) (ha : d131099 p = 1) (hb : d187818 p = 1) : d132527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187813 q = 1) : d132522 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187813, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43442 q ha hb
    | true =>
      simp only [d187813, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43321 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187814 q = 1) : d132523 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187814, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187814, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187815 q = 1) : d132524 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187815, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187815, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187816 q = 1) : d132525 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187816, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187816, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187817 q = 1) : d132526 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187817, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187817, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187818 q = 1) : d132527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187818, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187818, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43444 (p : Pattern) (ha : d131099 p = 1) (hb : d187824 p = 1) : d132533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187819 q = 1) : d132528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187819, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187819, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43443 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187820 q = 1) : d132529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187820, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187820, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187821 q = 1) : d132530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187821, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187821, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187822 q = 1) : d132531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187822, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187822, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187823 q = 1) : d132532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187823, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187823, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187824 q = 1) : d132533 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187824, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187824, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43445 (p : Pattern) (ha : d131099 p = 1) (hb : d187830 p = 1) : d132539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187825 q = 1) : d132534 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187825, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187825, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43444 q ha hb
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187826 q = 1) : d132535 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187826, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187826, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187827 q = 1) : d132536 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187827, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187827, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187828 q = 1) : d132537 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187828, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187828, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187829 q = 1) : d132538 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187829, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187829, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187830 q = 1) : d132539 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187830, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187830, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43446 (p : Pattern) (ha : d131099 p = 1) (hb : d187836 p = 1) : d132545 p = 1 := by
  have h0 (q : Pattern) (ha : d131099 q = 1) (hb : d187725 q = 1) : d132434 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187725, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43424 q ha hb
    | true =>
      simp only [d187725, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43427 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187744 q = 1) : d132453 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187744, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187744, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43430 q ha hb
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187745 q = 1) : d132454 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187745, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187745, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187772 q = 1) : d132481 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187772, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187772, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43435 q ha hb
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187773 q = 1) : d132482 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187773, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187773, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187774 q = 1) : d132483 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187774, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187774, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131099 q = 1) (hb : d187801 q = 1) : d132510 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187801, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187801, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43440 q ha hb
  have h8 (q : Pattern) (ha : d131099 q = 1) (hb : d187802 q = 1) : d132511 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187802, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187802, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131099 q = 1) (hb : d187803 q = 1) : d132512 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187803, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187803, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131099 q = 1) (hb : d187804 q = 1) : d132513 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187804, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187804, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131099 q = 1) (hb : d187831 q = 1) : d132540 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187831, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187831, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43445 q ha hb
  have h12 (q : Pattern) (ha : d131099 q = 1) (hb : d187832 q = 1) : d132541 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187832, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187832, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131099 q = 1) (hb : d187833 q = 1) : d132542 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187833, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187833, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131099 q = 1) (hb : d187834 q = 1) : d132543 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187834, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187834, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131099 q = 1) (hb : d187835 q = 1) : d132544 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d187835, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d187835, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131099 q = 1) (hb : d187836 q = 1) : d132545 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d187836, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d187836, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43447 (p : Pattern) (ha : d131099 p = 1) (hb : d187842 p = 1) : d132551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187837 q = 1) : d132546 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d187837, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43446 q ha hb
    | true =>
      simp only [d187837, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187838 q = 1) : d132547 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d187838, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187838, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187839 q = 1) : d132548 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d187839, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187839, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187840 q = 1) : d132549 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d187840, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187840, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187841 q = 1) : d132550 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d187841, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187841, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187842 q = 1) : d132551 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d187842, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187842, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43448 (p : Pattern) (ha : d131099 p = 1) (hb : d187848 p = 1) : d132557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187843 q = 1) : d132552 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d187843, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43447 q ha hb
    | true =>
      simp only [d187843, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187844 q = 1) : d132553 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d187844, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187844, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187845 q = 1) : d132554 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d187845, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187845, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187846 q = 1) : d132555 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d187846, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187846, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187847 q = 1) : d132556 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d187847, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187847, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187848 q = 1) : d132557 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d187848, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187848, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43449 (p : Pattern) (ha : d131099 p = 1) (hb : d187854 p = 1) : d132563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187849 q = 1) : d132558 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d187849, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43448 q ha hb
    | true =>
      simp only [d187849, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187850 q = 1) : d132559 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d187850, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187850, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187851 q = 1) : d132560 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d187851, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187851, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187852 q = 1) : d132561 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d187852, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187852, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187853 q = 1) : d132562 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d187853, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187853, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187854 q = 1) : d132563 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d187854, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187854, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43450 (p : Pattern) (ha : d131099 p = 1) (hb : d187860 p = 1) : d132569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187855 q = 1) : d132564 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d187855, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43449 q ha hb
    | true =>
      simp only [d187855, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187856 q = 1) : d132565 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d187856, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187856, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187857 q = 1) : d132566 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d187857, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187857, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187858 q = 1) : d132567 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d187858, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187858, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187859 q = 1) : d132568 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d187859, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187859, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187860 q = 1) : d132569 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d187860, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187860, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43451 (p : Pattern) (ha : d131099 p = 1) (hb : d187866 p = 1) : d132575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187861 q = 1) : d132570 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d187861, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43450 q ha hb
    | true =>
      simp only [d187861, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187862 q = 1) : d132571 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d187862, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187862, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187863 q = 1) : d132572 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d187863, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187863, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187864 q = 1) : d132573 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d187864, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187864, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187865 q = 1) : d132574 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d187865, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187865, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187866 q = 1) : d132575 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d187866, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187866, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43452 (p : Pattern) (ha : d131099 p = 1) (hb : d187872 p = 1) : d132581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187867 q = 1) : d132576 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d187867, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43451 q ha hb
    | true =>
      simp only [d187867, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187868 q = 1) : d132577 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d187868, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187868, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187869 q = 1) : d132578 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d187869, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187869, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187870 q = 1) : d132579 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d187870, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187870, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187871 q = 1) : d132580 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d187871, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187871, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187872 q = 1) : d132581 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d187872, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187872, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43453 (p : Pattern) (ha : d131099 p = 1) (hb : d187878 p = 1) : d132587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131099 q = 1) (hb : d187873 q = 1) : d132582 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d187873, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43452 q ha hb
    | true =>
      simp only [d187873, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131099 q = 1) (hb : d187874 q = 1) : d132583 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d187874, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187874, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131099 q = 1) (hb : d187875 q = 1) : d132584 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d187875, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187875, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131099 q = 1) (hb : d187876 q = 1) : d132585 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d187876, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187876, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131099 q = 1) (hb : d187877 q = 1) : d132586 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d187877, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187877, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131099 q = 1) (hb : d187878 q = 1) : d132587 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d187878, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187878, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43454 (p : Pattern) (ha : d100998 p = 1) (hb : d132049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100960 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
    | true =>
      simp only [d100960, d131985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100994 q = 1) (hb : d132045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100994, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d100994, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d100961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100995 q = 1) (hb : d132046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d100995, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100995, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100996 q = 1) (hb : d132047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d100996, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100996, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d100997 q = 1) (hb : d132048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d100997, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100997, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d100998 q = 1) (hb : d132049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d100998, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100998, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43455 (p : Pattern) (ha : d101004 p = 1) (hb : d132393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100999 q = 1) (hb : d132050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d100999, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d100999, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43454 q ha hb
  have h2 (q : Pattern) (ha : d101000 q = 1) (hb : d132389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101000, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101000, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101001 q = 1) (hb : d132390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101001, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101001, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101002 q = 1) (hb : d132391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101002, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101002, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101003 q = 1) (hb : d132392 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101003, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101003, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101004 q = 1) (hb : d132393 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101004, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101004, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43456 (p : Pattern) (ha : d101045 p = 1) (hb : d132403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d100993 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d100993, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43345 q ha hb
    | true =>
      simp only [d100993, d132008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43341 q ha hb
  have h3 (q : Pattern) (ha : d101035 q = 1) (hb : d132399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101035, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101035, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101041 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101042 q = 1) (hb : d132400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101042, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101042, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101043 q = 1) (hb : d132401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101043, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101043, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101044 q = 1) (hb : d132402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101044, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101044, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101045 q = 1) (hb : d132403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101045, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101045, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43457 (p : Pattern) (ha : d101057 p = 1) (hb : d132409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101046 q = 1) (hb : d132404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101046, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101046, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43456 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101053 q = 1) (hb : d132405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101053, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101053, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101054 q = 1) (hb : d132406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101054, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101054, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101055 q = 1) (hb : d132407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101055, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101055, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101056 q = 1) (hb : d132408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101056, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101056, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101057 q = 1) (hb : d132409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101057, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101057, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43458 (p : Pattern) (ha : d101063 p = 1) (hb : d132415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100975 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101005 q = 1) (hb : d132394 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101005, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101005, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43455 q ha hb
  have h3 (q : Pattern) (ha : d101006 q = 1) (hb : d132395 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101006, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101006, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101007 q = 1) (hb : d132396 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101007, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101007, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101008 q = 1) (hb : d132397 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101008, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101008, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101009 q = 1) (hb : d132398 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101009, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101009, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101058 q = 1) (hb : d132410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101058, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101058, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43457 q ha hb
  have h8 (q : Pattern) (ha : d101059 q = 1) (hb : d132411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101059, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101059, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101060 q = 1) (hb : d132412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101060, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101060, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101061 q = 1) (hb : d132413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101061, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101061, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101062 q = 1) (hb : d132414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101062, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101062, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101063 q = 1) (hb : d132415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101063, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101063, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43459 (p : Pattern) (ha : d101135 p = 1) (hb : d132421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101124 q = 1) (hb : d132416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101124, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43359 q ha hb
    | true =>
      simp only [d101124, d132416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43362 q ha hb
  have h3 (q : Pattern) (ha : d101125 q = 1) (hb : d132417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101125, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101125, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101131 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101132 q = 1) (hb : d132418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101132, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101132, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101133 q = 1) (hb : d132419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101133, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101133, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101134 q = 1) (hb : d132420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101134, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101134, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101135 q = 1) (hb : d132421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101135, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101135, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43460 (p : Pattern) (ha : d101148 p = 1) (hb : d132427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101136 q = 1) (hb : d132422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101136, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101136, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43459 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101143 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101144 q = 1) (hb : d132423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101144, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101144, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101145 q = 1) (hb : d132424 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101145, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101145, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101146 q = 1) (hb : d132425 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101146, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101146, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101147 q = 1) (hb : d132426 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101147, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101147, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101148 q = 1) (hb : d132427 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101148, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101148, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43461 (p : Pattern) (ha : d101154 p = 1) (hb : d132433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101149 q = 1) (hb : d132428 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101149, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101149, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43460 q ha hb
  have h2 (q : Pattern) (ha : d101150 q = 1) (hb : d132429 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101150, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101150, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101151 q = 1) (hb : d132430 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101151, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101151, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101152 q = 1) (hb : d132431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101152, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101152, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101153 q = 1) (hb : d132432 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101153, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101153, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101154 q = 1) (hb : d132433 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101154, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101154, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43462 (p : Pattern) (ha : d101245 p = 1) (hb : d132440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101234 q = 1) (hb : d132435 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101234, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43370 q ha hb
    | true =>
      simp only [d101234, d132435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43373 q ha hb
  have h3 (q : Pattern) (ha : d101235 q = 1) (hb : d132436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101235, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101235, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101241 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101242 q = 1) (hb : d132437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101242, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101242, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101243 q = 1) (hb : d132438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101243, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101243, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101244 q = 1) (hb : d132439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101244, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101244, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101245 q = 1) (hb : d132440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101245, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101245, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43463 (p : Pattern) (ha : d101258 p = 1) (hb : d132446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101246 q = 1) (hb : d132441 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101246, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101246, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43462 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101254 q = 1) (hb : d132442 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101254, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101254, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101255 q = 1) (hb : d132443 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101255, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101255, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101256 q = 1) (hb : d132444 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101256, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101256, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101257 q = 1) (hb : d132445 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101257, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101257, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101258 q = 1) (hb : d132446 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101258, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101258, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43464 (p : Pattern) (ha : d101264 p = 1) (hb : d132452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101259 q = 1) (hb : d132447 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101259, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101259, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43463 q ha hb
  have h2 (q : Pattern) (ha : d101260 q = 1) (hb : d132448 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101260, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101260, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101261 q = 1) (hb : d132449 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101261, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101261, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101262 q = 1) (hb : d132450 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101262, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101262, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101263 q = 1) (hb : d132451 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101263, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101263, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101264 q = 1) (hb : d132452 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101264, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101264, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43465 (p : Pattern) (ha : d101405 p = 1) (hb : d132456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h2 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h5 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42145 q ha hb
  have h9 (q : Pattern) (ha : d19088 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19089 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19090 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101404 q = 1) (hb : d132455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101404, d132455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101405 q = 1) (hb : d132456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101405, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101405, d132456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43466 (p : Pattern) (ha : d101411 p = 1) (hb : d132462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101406 q = 1) (hb : d132457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101406, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43465 q ha hb
    | true =>
      simp only [d101406, d132457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101407 q = 1) (hb : d132458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101407, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101407, d132458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101397 q = 1) (hb : d132180 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43380 q ha hb
    | true =>
      simp only [d101397, d132180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101398 q = 1) (hb : d132181 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101398, d132181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101408 q = 1) (hb : d132459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101408, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101408, d132459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101409 q = 1) (hb : d132460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101409, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101409, d132460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101410 q = 1) (hb : d132461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101410, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101410, d132461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101411 q = 1) (hb : d132462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101411, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101411, d132462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43467 (p : Pattern) (ha : d101436 p = 1) (hb : d132468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101416 q = 1) (hb : d132463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101416, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43466 q ha hb
    | true =>
      simp only [d101416, d132463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43385 q ha hb
  have h3 (q : Pattern) (ha : d101417 q = 1) (hb : d132464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101417, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101417, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101432 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101433 q = 1) (hb : d132465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101433, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101433, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101434 q = 1) (hb : d132466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101434, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101434, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101435 q = 1) (hb : d132467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101435, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101435, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101436 q = 1) (hb : d132468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101436, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101436, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43468 (p : Pattern) (ha : d101449 p = 1) (hb : d132474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101437 q = 1) (hb : d132469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101437, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101437, d132469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43467 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101444 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101445 q = 1) (hb : d132470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101445, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101445, d132470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101446 q = 1) (hb : d132471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101446, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101446, d132471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101447 q = 1) (hb : d132472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101447, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101447, d132472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101448 q = 1) (hb : d132473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101448, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101448, d132473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101449 q = 1) (hb : d132474 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101449, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101449, d132474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43469 (p : Pattern) (ha : d101455 p = 1) (hb : d132480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101450 q = 1) (hb : d132475 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101450, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101450, d132475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43468 q ha hb
  have h2 (q : Pattern) (ha : d101451 q = 1) (hb : d132476 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101451, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101451, d132476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101452 q = 1) (hb : d132477 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101452, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101452, d132477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101453 q = 1) (hb : d132478 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101453, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101453, d132478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101454 q = 1) (hb : d132479 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101454, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101454, d132479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101455 q = 1) (hb : d132480 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101455, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101455, d132480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43470 (p : Pattern) (ha : d101605 p = 1) (hb : d132485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h2 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h5 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42171 q ha hb
  have h9 (q : Pattern) (ha : d19323 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19324 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19325 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101604 q = 1) (hb : d132484 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101604, d132484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101605 q = 1) (hb : d132485 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101605, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101605, d132485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43471 (p : Pattern) (ha : d101611 p = 1) (hb : d132491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101606 q = 1) (hb : d132486 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101606, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43470 q ha hb
    | true =>
      simp only [d101606, d132486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101607 q = 1) (hb : d132487 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101607, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101607, d132487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101597 q = 1) (hb : d132238 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43392 q ha hb
    | true =>
      simp only [d101597, d132238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101598 q = 1) (hb : d132239 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101598, d132239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101608 q = 1) (hb : d132488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101608, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101608, d132488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101609 q = 1) (hb : d132489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101609, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101609, d132489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101610 q = 1) (hb : d132490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101610, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101610, d132490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101611 q = 1) (hb : d132491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101611, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101611, d132491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43472 (p : Pattern) (ha : d101636 p = 1) (hb : d132497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101616 q = 1) (hb : d132492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101616, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43471 q ha hb
    | true =>
      simp only [d101616, d132492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43397 q ha hb
  have h3 (q : Pattern) (ha : d101617 q = 1) (hb : d132493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101617, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101617, d132493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101633 q = 1) (hb : d132494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101633, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101633, d132494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101634 q = 1) (hb : d132495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101634, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101634, d132495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101635 q = 1) (hb : d132496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101635, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101635, d132496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101636 q = 1) (hb : d132497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101636, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101636, d132497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43473 (p : Pattern) (ha : d101649 p = 1) (hb : d132503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101637 q = 1) (hb : d132498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101637, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101637, d132498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43472 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101645 q = 1) (hb : d132499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101645, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101645, d132499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101646 q = 1) (hb : d132500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101646, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101646, d132500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101647 q = 1) (hb : d132501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101647, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101647, d132501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101648 q = 1) (hb : d132502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101648, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101648, d132502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101649 q = 1) (hb : d132503 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101649, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101649, d132503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43474 (p : Pattern) (ha : d101655 p = 1) (hb : d132509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101650 q = 1) (hb : d132504 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101650, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101650, d132504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43473 q ha hb
  have h2 (q : Pattern) (ha : d101651 q = 1) (hb : d132505 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101651, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101651, d132505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101652 q = 1) (hb : d132506 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101652, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101652, d132506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101653 q = 1) (hb : d132507 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101653, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101653, d132507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101654 q = 1) (hb : d132508 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101654, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101654, d132508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101655 q = 1) (hb : d132509 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101655, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101655, d132509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43475 (p : Pattern) (ha : d101776 p = 1) (hb : d132515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h2 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h5 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17169 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42197 q ha hb
  have h9 (q : Pattern) (ha : d19555 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19556 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19557 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d101775 q = 1) (hb : d132514 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d101775, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d101776 q = 1) (hb : d132515 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d101776, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101776, d132515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro43476 (p : Pattern) (ha : d101782 p = 1) (hb : d132521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101777 q = 1) (hb : d132516 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101777, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43475 q ha hb
    | true =>
      simp only [d101777, d132516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101778 q = 1) (hb : d132517 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101778, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101778, d132517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101768 q = 1) (hb : d132297 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43404 q ha hb
    | true =>
      simp only [d101768, d132297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101769 q = 1) (hb : d132298 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101769, d132298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101779 q = 1) (hb : d132518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d101779, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101779, d132518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101780 q = 1) (hb : d132519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d101780, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101780, d132519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101781 q = 1) (hb : d132520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d101781, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101781, d132520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d101782 q = 1) (hb : d132521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d101782, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101782, d132521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43477 (p : Pattern) (ha : d101807 p = 1) (hb : d132527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101787 q = 1) (hb : d132522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d101787, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43476 q ha hb
    | true =>
      simp only [d101787, d132522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43409 q ha hb
  have h3 (q : Pattern) (ha : d101788 q = 1) (hb : d132523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101788, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101788, d132523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101803 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101804 q = 1) (hb : d132524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101804, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101804, d132524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101805 q = 1) (hb : d132525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101805, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101805, d132525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101806 q = 1) (hb : d132526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101806, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101806, d132526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101807 q = 1) (hb : d132527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101807, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101807, d132527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43478 (p : Pattern) (ha : d101820 p = 1) (hb : d132533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101808 q = 1) (hb : d132528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101808, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101808, d132528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43477 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101815 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101816 q = 1) (hb : d132529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101816, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101816, d132529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101817 q = 1) (hb : d132530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101817, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101817, d132530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101818 q = 1) (hb : d132531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101818, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101818, d132531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101819 q = 1) (hb : d132532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101819, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101819, d132532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d101820 q = 1) (hb : d132533 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101820, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101820, d132533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43479 (p : Pattern) (ha : d101826 p = 1) (hb : d132539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101821 q = 1) (hb : d132534 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101821, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101821, d132534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43478 q ha hb
  have h2 (q : Pattern) (ha : d101822 q = 1) (hb : d132535 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101822, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101822, d132535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101823 q = 1) (hb : d132536 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101823, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101823, d132536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101824 q = 1) (hb : d132537 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101824, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101824, d132537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101825 q = 1) (hb : d132538 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101825, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101825, d132538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101826 q = 1) (hb : d132539 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101826, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101826, d132539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43480 (p : Pattern) (ha : d101832 p = 1) (hb : d132545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101155 q = 1) (hb : d132434 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101155, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43458 q ha hb
    | true =>
      simp only [d101155, d132434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43461 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101265 q = 1) (hb : d132453 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101265, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101265, d132453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43464 q ha hb
  have h3 (q : Pattern) (ha : d101266 q = 1) (hb : d132454 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101266, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101266, d132454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101456 q = 1) (hb : d132481 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101456, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101456, d132481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43469 q ha hb
  have h5 (q : Pattern) (ha : d101457 q = 1) (hb : d132482 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101457, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101457, d132482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101458 q = 1) (hb : d132483 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101458, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101458, d132483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101656 q = 1) (hb : d132510 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101656, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101656, d132510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43474 q ha hb
  have h8 (q : Pattern) (ha : d101657 q = 1) (hb : d132511 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101657, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101657, d132511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101658 q = 1) (hb : d132512 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101658, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101658, d132512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101659 q = 1) (hb : d132513 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101659, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101659, d132513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101827 q = 1) (hb : d132540 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101827, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101827, d132540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43479 q ha hb
  have h12 (q : Pattern) (ha : d101828 q = 1) (hb : d132541 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101828, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101828, d132541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101829 q = 1) (hb : d132542 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101829, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101829, d132542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101830 q = 1) (hb : d132543 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101830, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101830, d132543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101831 q = 1) (hb : d132544 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d101831, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d101831, d132544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d101832 q = 1) (hb : d132545 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d101832, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d101832, d132545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43481 (p : Pattern) (ha : d101838 p = 1) (hb : d132551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101833 q = 1) (hb : d132546 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d101833, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43480 q ha hb
    | true =>
      simp only [d101833, d132546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101834 q = 1) (hb : d132547 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d101834, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101834, d132547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101835 q = 1) (hb : d132548 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d101835, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101835, d132548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101836 q = 1) (hb : d132549 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d101836, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101836, d132549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101837 q = 1) (hb : d132550 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d101837, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101837, d132550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101838 q = 1) (hb : d132551 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d101838, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101838, d132551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43482 (p : Pattern) (ha : d101844 p = 1) (hb : d132557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101839 q = 1) (hb : d132552 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d101839, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43481 q ha hb
    | true =>
      simp only [d101839, d132552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101840 q = 1) (hb : d132553 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d101840, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101840, d132553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101841 q = 1) (hb : d132554 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d101841, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101841, d132554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101842 q = 1) (hb : d132555 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d101842, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101842, d132555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101843 q = 1) (hb : d132556 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d101843, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101843, d132556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101844 q = 1) (hb : d132557 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d101844, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101844, d132557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43483 (p : Pattern) (ha : d101850 p = 1) (hb : d132563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101845 q = 1) (hb : d132558 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d101845, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43482 q ha hb
    | true =>
      simp only [d101845, d132558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101846 q = 1) (hb : d132559 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d101846, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101846, d132559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101847 q = 1) (hb : d132560 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d101847, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101847, d132560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101848 q = 1) (hb : d132561 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d101848, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101848, d132561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101849 q = 1) (hb : d132562 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d101849, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101849, d132562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101850 q = 1) (hb : d132563 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d101850, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101850, d132563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43484 (p : Pattern) (ha : d101856 p = 1) (hb : d132569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101851 q = 1) (hb : d132564 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d101851, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43483 q ha hb
    | true =>
      simp only [d101851, d132564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101852 q = 1) (hb : d132565 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d101852, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101852, d132565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101853 q = 1) (hb : d132566 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d101853, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101853, d132566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101854 q = 1) (hb : d132567 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d101854, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101854, d132567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101855 q = 1) (hb : d132568 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d101855, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101855, d132568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101856 q = 1) (hb : d132569 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d101856, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101856, d132569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43485 (p : Pattern) (ha : d101862 p = 1) (hb : d132575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101857 q = 1) (hb : d132570 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d101857, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43484 q ha hb
    | true =>
      simp only [d101857, d132570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101858 q = 1) (hb : d132571 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d101858, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101858, d132571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101859 q = 1) (hb : d132572 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d101859, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101859, d132572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101860 q = 1) (hb : d132573 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d101860, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101860, d132573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101861 q = 1) (hb : d132574 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d101861, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101861, d132574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101862 q = 1) (hb : d132575 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d101862, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101862, d132575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43486 (p : Pattern) (ha : d101868 p = 1) (hb : d132581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101863 q = 1) (hb : d132576 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d101863, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43485 q ha hb
    | true =>
      simp only [d101863, d132576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101864 q = 1) (hb : d132577 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d101864, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101864, d132577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101865 q = 1) (hb : d132578 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d101865, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101865, d132578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101866 q = 1) (hb : d132579 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d101866, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101866, d132579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101867 q = 1) (hb : d132580 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d101867, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101867, d132580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101868 q = 1) (hb : d132581 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d101868, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101868, d132581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43487 (p : Pattern) (ha : d101874 p = 1) (hb : d132587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101869 q = 1) (hb : d132582 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d101869, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43486 q ha hb
    | true =>
      simp only [d101869, d132582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d101870 q = 1) (hb : d132583 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d101870, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101870, d132583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d101871 q = 1) (hb : d132584 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d101871, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101871, d132584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d101872 q = 1) (hb : d132585 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d101872, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101872, d132585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d101873 q = 1) (hb : d132586 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d101873, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101873, d132586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d101874 q = 1) (hb : d132587 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d101874, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101874, d132587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43488 (p : Pattern) (ha : d101879 p = 1) (hb : d132049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101875 q = 1) (hb : d132045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101875, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101875, d132045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9310 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101876 q = 1) (hb : d132046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101876, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101876, d132046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101877 q = 1) (hb : d132047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101877, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101877, d132047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101878 q = 1) (hb : d132048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101878, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101878, d132048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101879 q = 1) (hb : d132049 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101879, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101879, d132049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43489 (p : Pattern) (ha : d101885 p = 1) (hb : d132393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101880 q = 1) (hb : d132050 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101880, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101880, d132050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43488 q ha hb
  have h2 (q : Pattern) (ha : d101881 q = 1) (hb : d132389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101881, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101881, d132389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d101882 q = 1) (hb : d132390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101882, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101882, d132390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d101883 q = 1) (hb : d132391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101883, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101883, d132391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101884 q = 1) (hb : d132392 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101884, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101884, d132392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101885 q = 1) (hb : d132393 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101885, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101885, d132393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43490 (p : Pattern) (ha : d101895 p = 1) (hb : d132403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9401 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101891 q = 1) (hb : d132399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101891, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101891, d132399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9426 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101892 q = 1) (hb : d132400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101892, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101892, d132400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101893 q = 1) (hb : d132401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101893, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101893, d132401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101894 q = 1) (hb : d132402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101894, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101894, d132402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101895 q = 1) (hb : d132403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101895, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101895, d132403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43491 (p : Pattern) (ha : d101901 p = 1) (hb : d132409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101896 q = 1) (hb : d132404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101896, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101896, d132404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43490 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9437 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101897 q = 1) (hb : d132405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101897, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101897, d132405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101898 q = 1) (hb : d132406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101898, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101898, d132406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101899 q = 1) (hb : d132407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101899, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101899, d132407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101900 q = 1) (hb : d132408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101900, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101900, d132408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101901 q = 1) (hb : d132409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101901, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101901, d132409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43492 (p : Pattern) (ha : d101907 p = 1) (hb : d132415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9324 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101886 q = 1) (hb : d132394 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101886, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101886, d132394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43489 q ha hb
  have h3 (q : Pattern) (ha : d101887 q = 1) (hb : d132395 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101887, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101887, d132395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101888 q = 1) (hb : d132396 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101888, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101888, d132396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101889 q = 1) (hb : d132397 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101889, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101889, d132397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101890 q = 1) (hb : d132398 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101890, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101890, d132398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101902 q = 1) (hb : d132410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101902, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101902, d132410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43491 q ha hb
  have h8 (q : Pattern) (ha : d101903 q = 1) (hb : d132411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101903, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101903, d132411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101904 q = 1) (hb : d132412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101904, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101904, d132412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101905 q = 1) (hb : d132413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101905, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101905, d132413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101906 q = 1) (hb : d132414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101906, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101906, d132414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101907 q = 1) (hb : d132415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101907, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101907, d132415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43493 (p : Pattern) (ha : d101912 p = 1) (hb : d132421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101908 q = 1) (hb : d132417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101908, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101908, d132417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9547 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101909 q = 1) (hb : d132418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101909, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101909, d132418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101910 q = 1) (hb : d132419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101910, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101910, d132419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101911 q = 1) (hb : d132420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101911, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101911, d132420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101912 q = 1) (hb : d132421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101912, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101912, d132421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43494 (p : Pattern) (ha : d101918 p = 1) (hb : d132427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101913 q = 1) (hb : d132422 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101913, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101913, d132422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43493 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101914 q = 1) (hb : d132423 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101914, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101914, d132423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101915 q = 1) (hb : d132424 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101915, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101915, d132424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101916 q = 1) (hb : d132425 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101916, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101916, d132425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101917 q = 1) (hb : d132426 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101917, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101917, d132426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101918 q = 1) (hb : d132427 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101918, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101918, d132427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43495 (p : Pattern) (ha : d101924 p = 1) (hb : d132433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101919 q = 1) (hb : d132428 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101919, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101919, d132428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43494 q ha hb
  have h2 (q : Pattern) (ha : d101920 q = 1) (hb : d132429 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101920, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101920, d132429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101921 q = 1) (hb : d132430 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101921, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101921, d132430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101922 q = 1) (hb : d132431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101922, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101922, d132431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101923 q = 1) (hb : d132432 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101923, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101923, d132432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101924 q = 1) (hb : d132433 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101924, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101924, d132433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43496 (p : Pattern) (ha : d101930 p = 1) (hb : d132440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101926 q = 1) (hb : d132436 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101926, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101926, d132436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9716 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101927 q = 1) (hb : d132437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101927, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101927, d132437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101928 q = 1) (hb : d132438 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101928, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101928, d132438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101929 q = 1) (hb : d132439 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101929, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101929, d132439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101930 q = 1) (hb : d132440 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101930, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101930, d132440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43497 (p : Pattern) (ha : d101936 p = 1) (hb : d132446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101931 q = 1) (hb : d132441 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101931, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101931, d132441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43496 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101932 q = 1) (hb : d132442 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101932, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101932, d132442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101933 q = 1) (hb : d132443 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101933, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101933, d132443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101934 q = 1) (hb : d132444 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101934, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101934, d132444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101935 q = 1) (hb : d132445 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101935, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101935, d132445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101936 q = 1) (hb : d132446 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101936, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101936, d132446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43498 (p : Pattern) (ha : d101942 p = 1) (hb : d132452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101937 q = 1) (hb : d132447 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101937, d132447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43497 q ha hb
  have h2 (q : Pattern) (ha : d101938 q = 1) (hb : d132448 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101938, d132448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101939 q = 1) (hb : d132449 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101939, d132449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101940 q = 1) (hb : d132450 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101940, d132450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101941 q = 1) (hb : d132451 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101941, d132451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101942 q = 1) (hb : d132452 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101942, d132452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43499 (p : Pattern) (ha : d101949 p = 1) (hb : d132468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d132463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101945 q = 1) (hb : d132464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101945, d132464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101946 q = 1) (hb : d132465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101946, d132465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101947 q = 1) (hb : d132466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101947, d132466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101948 q = 1) (hb : d132467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101948, d132467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101949 q = 1) (hb : d132468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101949, d132468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
