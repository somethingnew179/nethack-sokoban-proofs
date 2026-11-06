import NetHack.Soko22Hazard87.AndIntroBlocks0350
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro87750 (p : Pattern) (ha : d212284 p = 1) (hb : d270826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212279 q = 1) (hb : d270821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212279, d270821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87749 q ha hb
    | true =>
      simp only [d212279, d270821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212280 q = 1) (hb : d270822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212280, d270822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212280, d270822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212281 q = 1) (hb : d270823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212281, d270823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212281, d270823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212282 q = 1) (hb : d270824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212282, d270824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212282, d270824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212283 q = 1) (hb : d270825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212283, d270825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212283, d270825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212284 q = 1) (hb : d270826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212284, d270826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212284, d270826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87751 (p : Pattern) (ha : d212290 p = 1) (hb : d270832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212285 q = 1) (hb : d270827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212285, d270827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87750 q ha hb
    | true =>
      simp only [d212285, d270827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212286 q = 1) (hb : d270828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212286, d270828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212286, d270828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212287 q = 1) (hb : d270829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212287, d270829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212287, d270829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212288 q = 1) (hb : d270830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212288, d270830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212288, d270830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212289 q = 1) (hb : d270831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212289, d270831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212289, d270831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212290 q = 1) (hb : d270832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212290, d270832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212290, d270832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87752 (p : Pattern) (ha : d212296 p = 1) (hb : d270838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212291 q = 1) (hb : d270833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212291, d270833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87751 q ha hb
    | true =>
      simp only [d212291, d270833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212292 q = 1) (hb : d270834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212292, d270834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212292, d270834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212293 q = 1) (hb : d270835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212293, d270835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212293, d270835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212294 q = 1) (hb : d270836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212294, d270836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212294, d270836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212295 q = 1) (hb : d270837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212295, d270837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212295, d270837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212296 q = 1) (hb : d270838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212296, d270838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212296, d270838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87753 (p : Pattern) (ha : d212302 p = 1) (hb : d270844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212297 q = 1) (hb : d270839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212297, d270839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87752 q ha hb
    | true =>
      simp only [d212297, d270839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212298 q = 1) (hb : d270840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212298, d270840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212298, d270840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212299 q = 1) (hb : d270841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212299, d270841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212299, d270841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212300 q = 1) (hb : d270842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212300, d270842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212300, d270842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212301 q = 1) (hb : d270843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212301, d270843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212301, d270843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212302 q = 1) (hb : d270844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212302, d270844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212302, d270844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87754 (p : Pattern) (ha : d212308 p = 1) (hb : d270850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212303 q = 1) (hb : d270845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212303, d270845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87753 q ha hb
    | true =>
      simp only [d212303, d270845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212304 q = 1) (hb : d270846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212304, d270846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212304, d270846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212305 q = 1) (hb : d270847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212305, d270847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212305, d270847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212306 q = 1) (hb : d270848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212306, d270848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212306, d270848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212307 q = 1) (hb : d270849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212307, d270849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212307, d270849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212308 q = 1) (hb : d270850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212308, d270850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212308, d270850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87755 (p : Pattern) (ha : d267844 p = 1) (hb : d324280 p = 1) : d270962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37632 q = 1) (hb : d267844 q = 1) : d270203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37632, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87273 q ha hb
    | true =>
      simp only [d37632, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87274 q ha hb
  have h2 (q : Pattern) (ha : d37633 q = 1) (hb : d267844 q = 1) : d270204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37633, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37633, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37634 q = 1) (hb : d267844 q = 1) : d270205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37634, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37634, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37635 q = 1) (hb : d267844 q = 1) : d270206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37635, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37635, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37636 q = 1) (hb : d267844 q = 1) : d270207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37636, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37636, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324280 q = 1) : d270962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324280, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324280, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro87756 (p : Pattern) (ha : d267844 p = 1) (hb : d324287 p = 1) : d270969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37980 q = 1) (hb : d267844 q = 1) : d270378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37980, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87312 q ha hb
    | true =>
      simp only [d37980, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87281 q ha hb
  have h2 (q : Pattern) (ha : d37981 q = 1) (hb : d267844 q = 1) : d270379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37981, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37981, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37982 q = 1) (hb : d267844 q = 1) : d270380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37982, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37982, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d37994 q = 1) (hb : d267844 q = 1) : d270392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37994, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87281 q ha hb
    | true =>
      simp only [d37994, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87314 q ha hb
  have h5 (q : Pattern) (ha : d37995 q = 1) (hb : d267844 q = 1) : d270393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37995, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37995, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37996 q = 1) (hb : d267844 q = 1) : d270394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37996, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37996, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37997 q = 1) (hb : d267844 q = 1) : d270395 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37997, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37997, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38013 q = 1) (hb : d267844 q = 1) : d270411 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38013, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87281 q ha hb
    | true =>
      simp only [d38013, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87282 q ha hb
  have h9 (q : Pattern) (ha : d38014 q = 1) (hb : d267844 q = 1) : d270412 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38014, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38014, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38015 q = 1) (hb : d267844 q = 1) : d270413 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38015, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38015, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38016 q = 1) (hb : d267844 q = 1) : d270414 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38016, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38016, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d267844 q = 1) (hb : d324286 q = 1) : d270968 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324286, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324286, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d267844 q = 1) (hb : d324287 q = 1) : d270969 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324287, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324287, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro87757 (p : Pattern) (ha : d267844 p = 1) (hb : d324293 p = 1) : d270975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324288 q = 1) : d270970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324288, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87756 q ha hb
    | true =>
      simp only [d324288, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324289 q = 1) : d270971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324289, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324289, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38019 q = 1) (hb : d267844 q = 1) : d270417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38019, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87283 q ha hb
    | true =>
      simp only [d38019, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38020 q = 1) (hb : d267844 q = 1) : d270418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38020, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38020, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324290 q = 1) : d270972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324290, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324290, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324291 q = 1) : d270973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324291, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324291, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d267844 q = 1) (hb : d324292 q = 1) : d270974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324292, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324292, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d267844 q = 1) (hb : d324293 q = 1) : d270975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324293, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324293, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro87758 (p : Pattern) (ha : d267844 p = 1) (hb : d324299 p = 1) : d270981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324294 q = 1) : d270976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324294, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87757 q ha hb
    | true =>
      simp only [d324294, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87284 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324295 q = 1) : d270977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324295, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324295, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324296 q = 1) : d270978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324296, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324296, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324297 q = 1) : d270979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324297, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324297, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324298 q = 1) : d270980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324298, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324298, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324299 q = 1) : d270981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324299, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324299, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87759 (p : Pattern) (ha : d267844 p = 1) (hb : d324305 p = 1) : d270987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37638 q = 1) (hb : d267844 q = 1) : d270209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37638, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87272 q ha hb
    | true =>
      simp only [d37638, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87275 q ha hb
  have h2 (q : Pattern) (ha : d37639 q = 1) (hb : d267844 q = 1) : d270210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37639, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37639, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324278 q = 1) : d270960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324278, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d324278, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324279 q = 1) : d270961 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324279, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324279, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324281 q = 1) : d270963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324281, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324281, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87755 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324282 q = 1) : d270964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324282, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324282, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d267844 q = 1) (hb : d324283 q = 1) : d270965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324283, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324283, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d267844 q = 1) (hb : d324284 q = 1) : d270966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324284, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324284, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d267844 q = 1) (hb : d324285 q = 1) : d270967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324285, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324285, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d267844 q = 1) (hb : d324300 q = 1) : d270982 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324300, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324300, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87758 q ha hb
  have h11 (q : Pattern) (ha : d267844 q = 1) (hb : d324301 q = 1) : d270983 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324301, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324301, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d267844 q = 1) (hb : d324302 q = 1) : d270984 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324302, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324302, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d267844 q = 1) (hb : d324303 q = 1) : d270985 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324303, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324303, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d267844 q = 1) (hb : d324304 q = 1) : d270986 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324304, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324304, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d267844 q = 1) (hb : d324305 q = 1) : d270987 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324305, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324305, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87760 (p : Pattern) (ha : d267844 p = 1) (hb : d324311 p = 1) : d270993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324306 q = 1) : d270988 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324306, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324306, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87759 q ha hb
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324307 q = 1) : d270989 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324307, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324307, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324308 q = 1) : d270990 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324308, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324308, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324309 q = 1) : d270991 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324309, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324309, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324310 q = 1) : d270992 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324310, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324310, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324311 q = 1) : d270993 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324311, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324311, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87761 (p : Pattern) (ha : d267844 p = 1) (hb : d324318 p = 1) : d271000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38276 q = 1) (hb : d267844 q = 1) : d270558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38276, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87342 q ha hb
    | true =>
      simp only [d38276, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87343 q ha hb
  have h2 (q : Pattern) (ha : d38277 q = 1) (hb : d267844 q = 1) : d270559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38277, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38277, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38278 q = 1) (hb : d267844 q = 1) : d270560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38278, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38278, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38279 q = 1) (hb : d267844 q = 1) : d270561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38279, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38279, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38280 q = 1) (hb : d267844 q = 1) : d270562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38280, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38280, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324318 q = 1) : d271000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324318, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324318, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro87762 (p : Pattern) (ha : d267844 p = 1) (hb : d324325 p = 1) : d271007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38572 q = 1) (hb : d267844 q = 1) : d270714 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38572, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87380 q ha hb
    | true =>
      simp only [d38572, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87350 q ha hb
  have h2 (q : Pattern) (ha : d38573 q = 1) (hb : d267844 q = 1) : d270715 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38573, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38573, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38574 q = 1) (hb : d267844 q = 1) : d270716 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38574, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38574, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38586 q = 1) (hb : d267844 q = 1) : d270728 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38586, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87350 q ha hb
    | true =>
      simp only [d38586, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87382 q ha hb
  have h5 (q : Pattern) (ha : d38587 q = 1) (hb : d267844 q = 1) : d270729 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38587, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38587, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38588 q = 1) (hb : d267844 q = 1) : d270730 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38588, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38588, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38589 q = 1) (hb : d267844 q = 1) : d270731 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38589, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38589, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38605 q = 1) (hb : d267844 q = 1) : d270747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38605, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87350 q ha hb
    | true =>
      simp only [d38605, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87351 q ha hb
  have h9 (q : Pattern) (ha : d38606 q = 1) (hb : d267844 q = 1) : d270748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38606, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38606, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38607 q = 1) (hb : d267844 q = 1) : d270749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38607, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38607, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38608 q = 1) (hb : d267844 q = 1) : d270750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38608, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38608, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d267844 q = 1) (hb : d324324 q = 1) : d271006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324324, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324324, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d267844 q = 1) (hb : d324325 q = 1) : d271007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324325, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324325, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro87763 (p : Pattern) (ha : d267844 p = 1) (hb : d324331 p = 1) : d271013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324326 q = 1) : d271008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324326, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87762 q ha hb
    | true =>
      simp only [d324326, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324327 q = 1) : d271009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324327, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324327, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38611 q = 1) (hb : d267844 q = 1) : d270753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38611, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87352 q ha hb
    | true =>
      simp only [d38611, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38612 q = 1) (hb : d267844 q = 1) : d270754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38612, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38612, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324328 q = 1) : d271010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324328, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324328, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324329 q = 1) : d271011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324329, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324329, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d267844 q = 1) (hb : d324330 q = 1) : d271012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324330, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324330, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d267844 q = 1) (hb : d324331 q = 1) : d271013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324331, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324331, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro87764 (p : Pattern) (ha : d267844 p = 1) (hb : d324339 p = 1) : d270515 p = 1 := by
  have h0 (q : Pattern) (ha : d5238 q = 1) (hb : d216468 q = 1) : d5238 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d324334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324335 q = 1) : d5239 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d267844, d324335, d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d267844, d324335, d5239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324336 q = 1) : d27181 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d324336, d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324336, d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d216468 q = 1) : d2047 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10406 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d38188 q = 1) (hb : d267844 q = 1) : d2048 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38188, d267844, d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38188, d267844, d2048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d38189 q = 1) (hb : d267844 q = 1) : d2061 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38189, d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38189, d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d267844 q = 1) (hb : d324337 q = 1) : d27182 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d324337, d27182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324337, d27182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d267844 q = 1) (hb : d324338 q = 1) : d27183 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d324338, d27183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324338, d27183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d267844 q = 1) (hb : d324339 q = 1) : d270515 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d324339, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324339, d270515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h11 p ha hb
theorem andIntro87765 (p : Pattern) (ha : d267844 p = 1) (hb : d324345 p = 1) : d270746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38566 q = 1) (hb : d267844 q = 1) : d270708 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38566, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38566, d270708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87331 q ha hb
  have h2 (q : Pattern) (ha : d38211 q = 1) (hb : d267844 q = 1) : d270496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38211, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87331 q ha hb
    | true =>
      simp only [d38211, d270496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38567 q = 1) (hb : d267844 q = 1) : d270709 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38567, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38567, d270709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38212 q = 1) (hb : d267844 q = 1) : d270497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38212, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38212, d270497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38568 q = 1) (hb : d267844 q = 1) : d270710 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38568, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38568, d270710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38569 q = 1) (hb : d267844 q = 1) : d270711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38569, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38569, d270711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38603 q = 1) (hb : d267844 q = 1) : d270745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38603, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38603, d270745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38580 q = 1) (hb : d267844 q = 1) : d270722 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38580, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38580, d270722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87334 q ha hb
  have h9 (q : Pattern) (ha : d38234 q = 1) (hb : d267844 q = 1) : d270516 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38234, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87334 q ha hb
    | true =>
      simp only [d38234, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d38581 q = 1) (hb : d267844 q = 1) : d270723 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38581, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38581, d270723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d267844 q = 1) (hb : d324340 q = 1) : d270516 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d324340, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87764 q ha hb
    | true =>
      simp only [d324340, d270516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d267844 q = 1) (hb : d324341 q = 1) : d270517 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d324341, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324341, d270517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d267844 q = 1) (hb : d324342 q = 1) : d270724 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d324342, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d324342, d270724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d267844 q = 1) (hb : d324343 q = 1) : d270725 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d324343, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324343, d270725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d267844 q = 1) (hb : d324344 q = 1) : d270726 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d324344, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d324344, d270726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d267844 q = 1) (hb : d324345 q = 1) : d270746 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324345, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324345, d270746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro87766 (p : Pattern) (ha : d267844 p = 1) (hb : d324351 p = 1) : d270752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324346 q = 1) : d270747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d324346, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87350 q hb ha
    | true =>
      simp only [d324346, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87765 q ha hb
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324347 q = 1) : d270748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d324347, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324347, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324348 q = 1) : d270749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d324348, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324348, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324349 q = 1) : d270750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d324349, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324349, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324350 q = 1) : d270751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324350, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324350, d270751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324351 q = 1) : d270752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324351, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324351, d270752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87767 (p : Pattern) (ha : d267844 p = 1) (hb : d324357 p = 1) : d270784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324352 q = 1) : d270753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324352, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87766 q ha hb
    | true =>
      simp only [d324352, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324353 q = 1) : d270754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324353, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324353, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324354 q = 1) : d270781 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324354, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324354, d270781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324355 q = 1) : d270782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324355, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324355, d270782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324356 q = 1) : d270783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324356, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324356, d270783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324357 q = 1) : d270784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324357, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324357, d270784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87768 (p : Pattern) (ha : d267844 p = 1) (hb : d324363 p = 1) : d271019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324358 q = 1) : d271014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324358, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87763 q ha hb
    | true =>
      simp only [d324358, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87767 q ha hb
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324359 q = 1) : d271015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324359, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324359, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324360 q = 1) : d271016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324360, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324360, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324361 q = 1) : d271017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324361, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324361, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324362 q = 1) : d271018 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324362, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324362, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324363 q = 1) : d271019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324363, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324363, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87769 (p : Pattern) (ha : d267844 p = 1) (hb : d324369 p = 1) : d271025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38282 q = 1) (hb : d267844 q = 1) : d270564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38282, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87341 q ha hb
    | true =>
      simp only [d38282, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87344 q ha hb
  have h2 (q : Pattern) (ha : d38283 q = 1) (hb : d267844 q = 1) : d270565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38283, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38283, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324316 q = 1) : d270998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324316, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d324316, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324317 q = 1) : d270999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324317, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324317, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324319 q = 1) : d271001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324319, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324319, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87761 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324320 q = 1) : d271002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324320, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324320, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d267844 q = 1) (hb : d324321 q = 1) : d271003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324321, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324321, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d267844 q = 1) (hb : d324322 q = 1) : d271004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324322, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324322, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d267844 q = 1) (hb : d324323 q = 1) : d271005 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324323, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324323, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d267844 q = 1) (hb : d324364 q = 1) : d271020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324364, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324364, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87768 q ha hb
  have h11 (q : Pattern) (ha : d267844 q = 1) (hb : d324365 q = 1) : d271021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324365, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324365, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d267844 q = 1) (hb : d324366 q = 1) : d271022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324366, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324366, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d267844 q = 1) (hb : d324367 q = 1) : d271023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324367, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324367, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d267844 q = 1) (hb : d324368 q = 1) : d271024 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324368, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324368, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d267844 q = 1) (hb : d324369 q = 1) : d271025 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324369, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324369, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87770 (p : Pattern) (ha : d267844 p = 1) (hb : d324375 p = 1) : d271031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324370 q = 1) : d271026 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324370, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324370, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87769 q ha hb
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324371 q = 1) : d271027 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324371, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324371, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324372 q = 1) : d271028 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324372, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324372, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324373 q = 1) : d271029 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324373, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324373, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324374 q = 1) : d271030 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324374, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324374, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324375 q = 1) : d271031 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324375, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324375, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87771 (p : Pattern) (ha : d267844 p = 1) (hb : d324381 p = 1) : d271037 p = 1 := by
  have h0 (q : Pattern) (ha : d267844 q = 1) (hb : d270959 q = 1) : d270959 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324312 q = 1) : d270994 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324312, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324312, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87760 q ha hb
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324313 q = 1) : d270995 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324313, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324313, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324314 q = 1) : d270996 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324314, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324314, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324315 q = 1) : d270997 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324315, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324315, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324376 q = 1) : d271032 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324376, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324376, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87770 q ha hb
  have h7 (q : Pattern) (ha : d267844 q = 1) (hb : d324377 q = 1) : d271033 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324377, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324377, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d267844 q = 1) (hb : d324378 q = 1) : d271034 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324378, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324378, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d267844 q = 1) (hb : d324379 q = 1) : d271035 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324379, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324379, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d267844 q = 1) (hb : d324380 q = 1) : d271036 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d324380, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324380, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d267844 q = 1) (hb : d324381 q = 1) : d271037 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d324381, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324381, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro87772 (p : Pattern) (ha : d267844 p = 1) (hb : d324387 p = 1) : d271043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324382 q = 1) : d271038 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d324382, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87771 q ha hb
    | true =>
      simp only [d324382, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324383 q = 1) : d271039 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d324383, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324383, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324384 q = 1) : d271040 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d324384, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324384, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324385 q = 1) : d271041 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d324385, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324385, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324386 q = 1) : d271042 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d324386, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324386, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324387 q = 1) : d271043 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d324387, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324387, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87773 (p : Pattern) (ha : d267844 p = 1) (hb : d324393 p = 1) : d271049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324388 q = 1) : d271044 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d324388, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87772 q ha hb
    | true =>
      simp only [d324388, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324389 q = 1) : d271045 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d324389, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324389, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324390 q = 1) : d271046 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d324390, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324390, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324391 q = 1) : d271047 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d324391, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324391, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324392 q = 1) : d271048 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d324392, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324392, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324393 q = 1) : d271049 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d324393, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324393, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87774 (p : Pattern) (ha : d267844 p = 1) (hb : d324399 p = 1) : d271055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324394 q = 1) : d271050 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d324394, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87773 q ha hb
    | true =>
      simp only [d324394, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324395 q = 1) : d271051 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d324395, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324395, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324396 q = 1) : d271052 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d324396, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324396, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324397 q = 1) : d271053 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d324397, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324397, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324398 q = 1) : d271054 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d324398, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324398, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324399 q = 1) : d271055 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d324399, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324399, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87775 (p : Pattern) (ha : d267844 p = 1) (hb : d324405 p = 1) : d271061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324400 q = 1) : d271056 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d324400, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87774 q ha hb
    | true =>
      simp only [d324400, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324401 q = 1) : d271057 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d324401, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324401, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324402 q = 1) : d271058 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d324402, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324402, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324403 q = 1) : d271059 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d324403, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324403, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324404 q = 1) : d271060 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d324404, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324404, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324405 q = 1) : d271061 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d324405, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324405, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87776 (p : Pattern) (ha : d267844 p = 1) (hb : d324411 p = 1) : d271067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324406 q = 1) : d271062 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d324406, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87775 q ha hb
    | true =>
      simp only [d324406, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324407 q = 1) : d271063 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d324407, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324407, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324408 q = 1) : d271064 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d324408, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324408, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324409 q = 1) : d271065 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d324409, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324409, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324410 q = 1) : d271066 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d324410, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324410, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324411 q = 1) : d271067 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d324411, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324411, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87777 (p : Pattern) (ha : d267844 p = 1) (hb : d324417 p = 1) : d271073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324412 q = 1) : d271068 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d324412, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87776 q ha hb
    | true =>
      simp only [d324412, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324413 q = 1) : d271069 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d324413, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324413, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324414 q = 1) : d271070 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d324414, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324414, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324415 q = 1) : d271071 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d324415, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324415, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324416 q = 1) : d271072 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d324416, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324416, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324417 q = 1) : d271073 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d324417, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324417, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87778 (p : Pattern) (ha : d267844 p = 1) (hb : d324423 p = 1) : d271079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d267844 q = 1) (hb : d324418 q = 1) : d271074 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d324418, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87777 q ha hb
    | true =>
      simp only [d324418, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d267844 q = 1) (hb : d324419 q = 1) : d271075 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d324419, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324419, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d267844 q = 1) (hb : d324420 q = 1) : d271076 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d324420, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324420, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d267844 q = 1) (hb : d324421 q = 1) : d271077 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d324421, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324421, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d267844 q = 1) (hb : d324422 q = 1) : d271078 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d324422, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324422, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d267844 q = 1) (hb : d324423 q = 1) : d271079 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d324423, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324423, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87779 (p : Pattern) (ha : d36090 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36026 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87405 q ha hb
    | true =>
      simp only [d36026, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d36086 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36086, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36087 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36087, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36088 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36088, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36089 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36089, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36090 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87780 (p : Pattern) (ha : d36097 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36026 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87405 q ha hb
    | true =>
      simp only [d36026, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d36086 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36086, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36087 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36087, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36088 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36088, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36089 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36033 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87407 q ha hb
    | true =>
      simp only [d36033, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d36093 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36093, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36094 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36094, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36095 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36095, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36096 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36096, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36097 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36097, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87781 (p : Pattern) (ha : d126906 p = 1) (hb : d270853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36033 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87407 q ha hb
    | true =>
      simp only [d36033, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36093, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36094 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36095 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36096 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d270853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87782 (p : Pattern) (ha : d126930 p = 1) (hb : d270863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36069 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87412 q ha hb
    | true =>
      simp only [d36069, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d270859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d270860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d270861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d270862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d270863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87783 (p : Pattern) (ha : d126936 p = 1) (hb : d270869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87779 q ha hb
    | true =>
      simp only [d36098, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87780 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36099 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d270851 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d270852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d270854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87781 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d270855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d270856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d270857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d270858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d270864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87782 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d270865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d270866 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d270867 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d270868 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d270869 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87784 (p : Pattern) (ha : d126942 p = 1) (hb : d270875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d270870 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87783 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d270871 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d270872 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d270873 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d270874 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d270875 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro87785 (p : Pattern) (ha : d36302 p = 1) (hb : d127013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36297 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87443 q ha hb
    | true =>
      simp only [d36297, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87444 q ha hb
  have h5 (q : Pattern) (ha : d36298 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36298, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36299 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36299, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36300 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36300, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36301 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36301, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36302 q = 1) (hb : d127013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87786 (p : Pattern) (ha : d36312 p = 1) (hb : d127032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36297 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87443 q ha hb
    | true =>
      simp only [d36297, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87444 q ha hb
  have h4 (q : Pattern) (ha : d36298 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36298, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36299 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36299, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36300 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36300, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36301 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36307 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87446 q ha hb
    | true =>
      simp only [d36307, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87447 q ha hb
  have h13 (q : Pattern) (ha : d36308 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36308, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36309 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36309, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36310 q = 1) (hb : d127030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36310, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36311 q = 1) (hb : d127031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36311, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36312 q = 1) (hb : d127032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36312, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87787 (p : Pattern) (ha : d127041 p = 1) (hb : d270878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36307 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87446 q ha hb
    | true =>
      simp only [d36307, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87447 q ha hb
  have h3 (q : Pattern) (ha : d36308 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36308, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36309 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36309, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36310 q = 1) (hb : d127039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36311 q = 1) (hb : d127040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127041 q = 1) (hb : d270878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127041, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127041, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87788 (p : Pattern) (ha : d127090 p = 1) (hb : d270889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d270884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87483 q hb ha
    | true =>
      simp only [d127079, d270884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87453 q hb ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d270885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127087 q = 1) (hb : d270886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127088 q = 1) (hb : d270887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127089 q = 1) (hb : d270888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127090 q = 1) (hb : d270889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87789 (p : Pattern) (ha : d127096 p = 1) (hb : d270895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d127033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87785 q ha hb
    | true =>
      simp only [d36313, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87786 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36314 q = 1) (hb : d127036 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127037 q = 1) (hb : d270876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127037, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127037, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127038 q = 1) (hb : d270877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127038, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127038, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127042 q = 1) (hb : d270879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127042, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127042, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87787 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127043 q = 1) (hb : d270880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127043, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127043, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127044 q = 1) (hb : d270881 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127044, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127044, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127045 q = 1) (hb : d270882 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127045, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127045, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127046 q = 1) (hb : d270883 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127046, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127046, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127091 q = 1) (hb : d270890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127091, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87788 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127092 q = 1) (hb : d270891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127092, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127093 q = 1) (hb : d270892 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127093, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127094 q = 1) (hb : d270893 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127094, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127095 q = 1) (hb : d270894 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127095, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127096 q = 1) (hb : d270895 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127096, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87790 (p : Pattern) (ha : d127102 p = 1) (hb : d270901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d270896 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87789 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d270897 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d270898 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d270899 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d270900 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d270901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87791 (p : Pattern) (ha : d36634 p = 1) (hb : d127179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36629 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87494 q ha hb
    | true =>
      simp only [d36629, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87495 q ha hb
  have h5 (q : Pattern) (ha : d36630 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36630, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36631 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36631, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36632 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36632, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36633 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36633, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36634 q = 1) (hb : d127179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87792 (p : Pattern) (ha : d36644 p = 1) (hb : d127198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36629 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87494 q ha hb
    | true =>
      simp only [d36629, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87495 q ha hb
  have h4 (q : Pattern) (ha : d36630 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36630, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36631 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36631, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36632 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36632, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36633 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127184 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36639 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87497 q ha hb
    | true =>
      simp only [d36639, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87498 q ha hb
  have h13 (q : Pattern) (ha : d36640 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36640, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36641 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36641, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36642 q = 1) (hb : d127196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36642, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36643 q = 1) (hb : d127197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36643, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36644 q = 1) (hb : d127198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36644, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87793 (p : Pattern) (ha : d127207 p = 1) (hb : d270905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36639 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87497 q ha hb
    | true =>
      simp only [d36639, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87498 q ha hb
  have h3 (q : Pattern) (ha : d36640 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36640, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36641 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36641, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36642 q = 1) (hb : d127205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36643 q = 1) (hb : d127206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127207 q = 1) (hb : d270905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127207, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127207, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87794 (p : Pattern) (ha : d127261 p = 1) (hb : d270916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127250 q = 1) (hb : d270911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127250, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87537 q hb ha
    | true =>
      simp only [d127250, d270911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87506 q hb ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d270912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127258 q = 1) (hb : d270913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127259 q = 1) (hb : d270914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127260 q = 1) (hb : d270915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127261 q = 1) (hb : d270916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87795 (p : Pattern) (ha : d127267 p = 1) (hb : d270922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d127199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87791 q ha hb
    | true =>
      simp only [d36645, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87792 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36646 q = 1) (hb : d127202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127203 q = 1) (hb : d270903 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127203, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127203, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127204 q = 1) (hb : d270904 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127204, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127204, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127208 q = 1) (hb : d270906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127208, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127208, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87793 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127209 q = 1) (hb : d270907 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127209, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127209, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127210 q = 1) (hb : d270908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127210, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127210, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127211 q = 1) (hb : d270909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127211, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127211, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127212 q = 1) (hb : d270910 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127212, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127212, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127262 q = 1) (hb : d270917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127262, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87794 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127263 q = 1) (hb : d270918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127263, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127264 q = 1) (hb : d270919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127264, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127265 q = 1) (hb : d270920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127265, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127266 q = 1) (hb : d270921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127266, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127267 q = 1) (hb : d270922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127267, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87796 (p : Pattern) (ha : d127273 p = 1) (hb : d270928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d270923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87795 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d270924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d270925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d270926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d270927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d270928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87797 (p : Pattern) (ha : d37065 p = 1) (hb : d127395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d37060 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37060, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87555 q ha hb
    | true =>
      simp only [d37060, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87556 q ha hb
  have h5 (q : Pattern) (ha : d37061 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37061, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d37062 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d37062, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37063 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37063, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d37064 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37064, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d37065 q = 1) (hb : d127395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37065, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37065, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87798 (p : Pattern) (ha : d37075 p = 1) (hb : d127417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37060 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37060, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87555 q ha hb
    | true =>
      simp only [d37060, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87556 q ha hb
  have h4 (q : Pattern) (ha : d37061 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37061, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d37062 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d37062, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37063 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37063, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37064 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37064, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d37070 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87558 q ha hb
    | true =>
      simp only [d37070, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87559 q ha hb
  have h13 (q : Pattern) (ha : d37071 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d37071, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d37072 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37072, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d37073 q = 1) (hb : d127415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37073, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d37074 q = 1) (hb : d127416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37074, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d37075 q = 1) (hb : d127417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37075, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37075, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87799 (p : Pattern) (ha : d127442 p = 1) (hb : d270933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37070 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87558 q ha hb
    | true =>
      simp only [d37070, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87559 q ha hb
  have h3 (q : Pattern) (ha : d37071 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37071, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37072 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37072, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37073 q = 1) (hb : d127440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37074 q = 1) (hb : d127441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127442 q = 1) (hb : d270933 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127442, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127442, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87800 (p : Pattern) (ha : d37376 p = 1) (hb : d127508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37361 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37361, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87598 q ha hb
    | true =>
      simp only [d37361, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87566 q ha hb
  have h2 (q : Pattern) (ha : d37362 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37362, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37362, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37363 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37363, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37363, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d37366 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37366, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87566 q ha hb
    | true =>
      simp only [d37366, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87600 q ha hb
  have h5 (q : Pattern) (ha : d37367 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37367, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37367, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37368 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37368, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37368, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37369 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37369, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37369, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37366 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37366, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87566 q ha hb
    | true =>
      simp only [d37366, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87567 q ha hb
  have h9 (q : Pattern) (ha : d37367 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37367, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37367, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d37368 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37368, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37368, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d37374 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37374, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37374, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d37375 q = 1) (hb : d127507 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d37375, d127507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d37375, d127507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d37376 q = 1) (hb : d127508 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d37376, d127508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d37376, d127508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro87801 (p : Pattern) (ha : d37390 p = 1) (hb : d127514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37377 q = 1) (hb : d127509 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37377, d127509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87800 q ha hb
    | true =>
      simp only [d37377, d127509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d37378 q = 1) (hb : d127510 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d37378, d127510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37378, d127510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37385 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37385, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87568 q ha hb
    | true =>
      simp only [d37385, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37386 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d37386, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37386, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37387 q = 1) (hb : d127511 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d37387, d127511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37387, d127511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37388 q = 1) (hb : d127512 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d37388, d127512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d37388, d127512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d37389 q = 1) (hb : d127513 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d37389, d127513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d37389, d127513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d37390 q = 1) (hb : d127514 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d37390, d127514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d37390, d127514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87802 (p : Pattern) (ha : d127538 p = 1) (hb : d270944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127519 q = 1) (hb : d270939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127519, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87801 q hb ha
    | true =>
      simp only [d127519, d270939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87569 q hb ha
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d270940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127535 q = 1) (hb : d270941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127536 q = 1) (hb : d270942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127537 q = 1) (hb : d270943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127538 q = 1) (hb : d270944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87803 (p : Pattern) (ha : d127551 p = 1) (hb : d270950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127327 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d127418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87797 q ha hb
    | true =>
      simp only [d37076, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37077 q = 1) (hb : d127437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127438 q = 1) (hb : d270931 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127438, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127438, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127439 q = 1) (hb : d270932 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127439, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127439, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127443 q = 1) (hb : d270934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127443, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127443, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87799 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127445 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127446 q = 1) (hb : d270935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127446, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127446, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127447 q = 1) (hb : d270936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127447, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127447, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127448 q = 1) (hb : d270937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127448, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127448, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127449 q = 1) (hb : d270938 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127449, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127449, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127539 q = 1) (hb : d270945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127539, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87802 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127547 q = 1) (hb : d270946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127547, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127548 q = 1) (hb : d270947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127548, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127549 q = 1) (hb : d270948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127549, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127550 q = 1) (hb : d270949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127550, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127551 q = 1) (hb : d270950 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127551, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87804 (p : Pattern) (ha : d127557 p = 1) (hb : d270956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d270951 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87803 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d270952 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d270953 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d270954 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d270955 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d270956 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87805 (p : Pattern) (ha : d211633 p = 1) (hb : d270198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d211613 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211530 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211530, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87629 q ha hb
    | true =>
      simp only [d211530, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87630 q ha hb
  have h5 (q : Pattern) (ha : d211614 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211614, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d211614, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d211629 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d211630 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211630, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211630, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d211631 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211631, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211631, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211632 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211632, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211632, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211633 q = 1) (hb : d270198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211633, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211633, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87806 (p : Pattern) (ha : d211655 p = 1) (hb : d270208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211530 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211530, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87629 q ha hb
    | true =>
      simp only [d211530, d270193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87630 q ha hb
  have h4 (q : Pattern) (ha : d211614 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211614, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d211614, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d211629 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d211630 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211630, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d211630, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d211631 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211631, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211631, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211632 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211632, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211632, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d211639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d211644 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d211647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d211540 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211540, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87632 q ha hb
    | true =>
      simp only [d211540, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87633 q ha hb
  have h13 (q : Pattern) (ha : d211648 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211648, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d211648, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d211651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211652 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211652, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211652, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211653 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211653, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d211653, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d211654 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211654, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d211654, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d211655 q = 1) (hb : d270208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211655, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d211655, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87807 (p : Pattern) (ha : d211680 p = 1) (hb : d270962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211540 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211540, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87632 q ha hb
    | true =>
      simp only [d211540, d270203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87633 q ha hb
  have h3 (q : Pattern) (ha : d211648 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211648, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211648, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d211651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211652 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211652, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211652, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211678 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211678, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211678, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211679 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211679, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211679, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211680 q = 1) (hb : d270962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211680, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211680, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87808 (p : Pattern) (ha : d211793 p = 1) (hb : d270969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211742 q = 1) (hb : d270378 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d211742, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87665 q ha hb
    | true =>
      simp only [d211742, d270378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87667 q ha hb
  have h2 (q : Pattern) (ha : d211743 q = 1) (hb : d270379 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d211743, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211743, d270379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211744 q = 1) (hb : d270380 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d211744, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211744, d270380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211756 q = 1) (hb : d270392 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d211756, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87667 q ha hb
    | true =>
      simp only [d211756, d270392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87668 q ha hb
  have h5 (q : Pattern) (ha : d211757 q = 1) (hb : d270393 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d211757, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211757, d270393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211758 q = 1) (hb : d270394 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d211758, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211758, d270394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211759 q = 1) (hb : d270395 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d211759, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211759, d270395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211779 q = 1) (hb : d270411 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d211779, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87667 q ha hb
    | true =>
      simp only [d211779, d270411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87672 q ha hb
  have h9 (q : Pattern) (ha : d211780 q = 1) (hb : d270412 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d211780, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211780, d270412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211781 q = 1) (hb : d270413 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d211781, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211781, d270413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d211782 q = 1) (hb : d270414 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d211782, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211782, d270414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d211792 q = 1) (hb : d270968 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d211792, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211792, d270968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211793 q = 1) (hb : d270969 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d211793, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211793, d270969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro87809 (p : Pattern) (ha : d211799 p = 1) (hb : d270975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211794 q = 1) (hb : d270970 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d211794, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87808 q ha hb
    | true =>
      simp only [d211794, d270970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d211795 q = 1) (hb : d270971 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d211795, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211795, d270971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211785 q = 1) (hb : d270417 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d211785, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87673 q ha hb
    | true =>
      simp only [d211785, d270417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d211786 q = 1) (hb : d270418 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d211786, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211786, d270418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211796 q = 1) (hb : d270972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d211796, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d211796, d270972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211797 q = 1) (hb : d270973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d211797, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d211797, d270973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d211798 q = 1) (hb : d270974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d211798, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211798, d270974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d211799 q = 1) (hb : d270975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d211799, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211799, d270975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro87810 (p : Pattern) (ha : d211824 p = 1) (hb : d270981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211804 q = 1) (hb : d270976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211804, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87809 q ha hb
    | true =>
      simp only [d211804, d270976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87679 q ha hb
  have h3 (q : Pattern) (ha : d211805 q = 1) (hb : d270977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d211805, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211805, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d211820 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211821 q = 1) (hb : d270978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d211821, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211821, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211822 q = 1) (hb : d270979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d211822, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211822, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211823 q = 1) (hb : d270980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d211823, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211823, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d211824 q = 1) (hb : d270981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d211824, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211824, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87811 (p : Pattern) (ha : d211837 p = 1) (hb : d270987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211548 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211656 q = 1) (hb : d270209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211656, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87805 q ha hb
    | true =>
      simp only [d211656, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87806 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211675 q = 1) (hb : d270210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211675, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d211675, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d211676 q = 1) (hb : d270960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211676, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d211676, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d211677 q = 1) (hb : d270961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211677, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211677, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211681 q = 1) (hb : d270963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211681, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211681, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87807 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d211683 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d211684 q = 1) (hb : d270964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211684, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d211684, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d211685 q = 1) (hb : d270965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211685, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d211685, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d211686 q = 1) (hb : d270966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211686, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d211686, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d211687 q = 1) (hb : d270967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211687, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211687, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d211825 q = 1) (hb : d270982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d211825, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d211825, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87810 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d211832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d211833 q = 1) (hb : d270983 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d211833, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d211833, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d211834 q = 1) (hb : d270984 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d211834, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d211834, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d211835 q = 1) (hb : d270985 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d211835, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d211835, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d211836 q = 1) (hb : d270986 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d211836, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d211836, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d211837 q = 1) (hb : d270987 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d211837, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d211837, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87812 (p : Pattern) (ha : d211843 p = 1) (hb : d270993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d211838 q = 1) (hb : d270988 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d211838, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211838, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87811 q ha hb
  have h2 (q : Pattern) (ha : d211839 q = 1) (hb : d270989 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d211839, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211839, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d211840 q = 1) (hb : d270990 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d211840, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211840, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d211841 q = 1) (hb : d270991 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d211841, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211841, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d211842 q = 1) (hb : d270992 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d211842, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211842, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d211843 q = 1) (hb : d270993 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d211843, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d211843, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87813 (p : Pattern) (ha : d212055 p = 1) (hb : d270553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211987 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d211996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d212035 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d211961 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211961, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87698 q ha hb
    | true =>
      simp only [d211961, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87699 q ha hb
  have h5 (q : Pattern) (ha : d212036 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212036, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212036, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d212051 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d212052 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212052, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212052, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d212053 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212053, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212053, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212054 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212054, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212054, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212055 q = 1) (hb : d270553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212055, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212055, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87814 (p : Pattern) (ha : d212077 p = 1) (hb : d270563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211987 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d211996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d211961 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211961, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87698 q ha hb
    | true =>
      simp only [d211961, d270548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87699 q ha hb
  have h4 (q : Pattern) (ha : d212036 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212036, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212036, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d212051 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d212052 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212052, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212052, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d212053 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212053, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212053, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212054 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212054, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212054, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d212061 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d212066 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d212069 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d211971 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211971, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87701 q ha hb
    | true =>
      simp only [d211971, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87702 q ha hb
  have h13 (q : Pattern) (ha : d212070 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212070, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d212070, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d212073 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212074 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212074, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212074, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212075 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212075, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d212075, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d212076 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212076, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d212076, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d212077 q = 1) (hb : d270563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212077, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d212077, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87815 (p : Pattern) (ha : d212102 p = 1) (hb : d271000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d212069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d211971 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d211971, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87701 q ha hb
    | true =>
      simp only [d211971, d270558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87702 q ha hb
  have h3 (q : Pattern) (ha : d212070 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212070, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212070, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d212073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212074 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212074, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212074, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212100 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212100, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212100, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212101 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212101, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212101, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212102 q = 1) (hb : d271000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212102, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212102, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87816 (p : Pattern) (ha : d212210 p = 1) (hb : d271007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212159 q = 1) (hb : d270714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212159, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87729 q ha hb
    | true =>
      simp only [d212159, d270714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87731 q ha hb
  have h2 (q : Pattern) (ha : d212160 q = 1) (hb : d270715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212160, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212160, d270715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212161 q = 1) (hb : d270716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d212161, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212161, d270716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212173 q = 1) (hb : d270728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212173, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87731 q ha hb
    | true =>
      simp only [d212173, d270728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87732 q ha hb
  have h5 (q : Pattern) (ha : d212174 q = 1) (hb : d270729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212174, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212174, d270729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212175 q = 1) (hb : d270730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d212175, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212175, d270730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212176 q = 1) (hb : d270731 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212176, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212176, d270731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212196 q = 1) (hb : d270747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d212196, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87731 q ha hb
    | true =>
      simp only [d212196, d270747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87736 q ha hb
  have h9 (q : Pattern) (ha : d212197 q = 1) (hb : d270748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d212197, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212197, d270748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212198 q = 1) (hb : d270749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d212198, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212198, d270749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212199 q = 1) (hb : d270750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d212199, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212199, d270750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d212209 q = 1) (hb : d271006 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212209, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212209, d271006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212210 q = 1) (hb : d271007 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212210, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212210, d271007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro87817 (p : Pattern) (ha : d212216 p = 1) (hb : d271013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212211 q = 1) (hb : d271008 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212211, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87816 q ha hb
    | true =>
      simp only [d212211, d271008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212212 q = 1) (hb : d271009 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212212, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212212, d271009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212202 q = 1) (hb : d270753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212202, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87737 q ha hb
    | true =>
      simp only [d212202, d270753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212203 q = 1) (hb : d270754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212203, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212203, d270754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212213 q = 1) (hb : d271010 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212213, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212213, d271010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212214 q = 1) (hb : d271011 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212214, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212214, d271011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d212215 q = 1) (hb : d271012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212215, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212215, d271012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d212216 q = 1) (hb : d271013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212216, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212216, d271013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro87818 (p : Pattern) (ha : d212241 p = 1) (hb : d271019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d212208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d212221 q = 1) (hb : d271014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212221, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87817 q ha hb
    | true =>
      simp only [d212221, d271014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87743 q ha hb
  have h3 (q : Pattern) (ha : d212222 q = 1) (hb : d271015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212222, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212222, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d212237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212238 q = 1) (hb : d271016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212238, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212238, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212239 q = 1) (hb : d271017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212239, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212239, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212240 q = 1) (hb : d271018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212240, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212240, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212241 q = 1) (hb : d271019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212241, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212241, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87819 (p : Pattern) (ha : d212254 p = 1) (hb : d271025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211979 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212078 q = 1) (hb : d270564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212078, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87813 q ha hb
    | true =>
      simp only [d212078, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87814 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d212096 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212097 q = 1) (hb : d270565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212097, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212097, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212098 q = 1) (hb : d270998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212098, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212098, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212099 q = 1) (hb : d270999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212099, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212099, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212103 q = 1) (hb : d271001 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212103, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212103, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87815 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d212105 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212106 q = 1) (hb : d271002 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212106, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212106, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212107 q = 1) (hb : d271003 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212107, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212107, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d212108 q = 1) (hb : d271004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212108, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212108, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d212109 q = 1) (hb : d271005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212109, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212109, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212242 q = 1) (hb : d271020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212242, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212242, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87818 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d212249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212250 q = 1) (hb : d271021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212250, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212250, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212251 q = 1) (hb : d271022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212251, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212251, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d212252 q = 1) (hb : d271023 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212252, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212252, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d212253 q = 1) (hb : d271024 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212253, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212253, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d212254 q = 1) (hb : d271025 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212254, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212254, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87820 (p : Pattern) (ha : d212260 p = 1) (hb : d271031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212255 q = 1) (hb : d271026 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212255, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212255, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87819 q ha hb
  have h2 (q : Pattern) (ha : d212256 q = 1) (hb : d271027 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212256, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212256, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212257 q = 1) (hb : d271028 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212257, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212257, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212258 q = 1) (hb : d271029 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212258, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212258, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212259 q = 1) (hb : d271030 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212259, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212259, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212260 q = 1) (hb : d271031 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212260, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212260, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87821 (p : Pattern) (ha : d212266 p = 1) (hb : d271037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d270902 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87784 q ha hb
    | true =>
      simp only [d127103, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87790 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d270929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87796 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d270930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d270957 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87804 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d270958 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d270959 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d211844 q = 1) (hb : d270994 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d211844, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211844, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87812 q ha hb
  have h8 (q : Pattern) (ha : d211845 q = 1) (hb : d270995 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d211845, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211845, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d211846 q = 1) (hb : d270996 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d211846, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d211846, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d211847 q = 1) (hb : d270997 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d211847, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d211847, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212261 q = 1) (hb : d271032 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212261, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212261, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87820 q ha hb
  have h12 (q : Pattern) (ha : d212262 q = 1) (hb : d271033 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212262, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212262, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212263 q = 1) (hb : d271034 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212263, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212263, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212264 q = 1) (hb : d271035 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212264, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212264, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212265 q = 1) (hb : d271036 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212265, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212265, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212266 q = 1) (hb : d271037 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212266, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212266, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro87822 (p : Pattern) (ha : d212272 p = 1) (hb : d271043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212267 q = 1) (hb : d271038 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212267, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87821 q ha hb
    | true =>
      simp only [d212267, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212268 q = 1) (hb : d271039 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212268, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212268, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212269 q = 1) (hb : d271040 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212269, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212269, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212270 q = 1) (hb : d271041 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212270, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212270, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212271 q = 1) (hb : d271042 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212271, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212271, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212272 q = 1) (hb : d271043 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212272, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212272, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87823 (p : Pattern) (ha : d212278 p = 1) (hb : d271049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212273 q = 1) (hb : d271044 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212273, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87822 q ha hb
    | true =>
      simp only [d212273, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212274 q = 1) (hb : d271045 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212274, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212274, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212275 q = 1) (hb : d271046 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212275, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212275, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212276 q = 1) (hb : d271047 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212276, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212276, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212277 q = 1) (hb : d271048 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212277, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212277, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212278 q = 1) (hb : d271049 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212278, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212278, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87824 (p : Pattern) (ha : d212284 p = 1) (hb : d271055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212279 q = 1) (hb : d271050 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212279, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87823 q ha hb
    | true =>
      simp only [d212279, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212280 q = 1) (hb : d271051 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212280, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212280, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212281 q = 1) (hb : d271052 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212281, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212281, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212282 q = 1) (hb : d271053 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212282, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212282, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212283 q = 1) (hb : d271054 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212283, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212283, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212284 q = 1) (hb : d271055 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212284, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212284, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87825 (p : Pattern) (ha : d212290 p = 1) (hb : d271061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212285 q = 1) (hb : d271056 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212285, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87824 q ha hb
    | true =>
      simp only [d212285, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212286 q = 1) (hb : d271057 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212286, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212286, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212287 q = 1) (hb : d271058 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212287, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212287, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212288 q = 1) (hb : d271059 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212288, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212288, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212289 q = 1) (hb : d271060 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212289, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212289, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212290 q = 1) (hb : d271061 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212290, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212290, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87826 (p : Pattern) (ha : d212296 p = 1) (hb : d271067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212291 q = 1) (hb : d271062 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212291, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87825 q ha hb
    | true =>
      simp only [d212291, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212292 q = 1) (hb : d271063 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212292, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212292, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212293 q = 1) (hb : d271064 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212293, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212293, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212294 q = 1) (hb : d271065 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212294, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212294, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212295 q = 1) (hb : d271066 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212295, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212295, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212296 q = 1) (hb : d271067 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212296, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212296, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87827 (p : Pattern) (ha : d212302 p = 1) (hb : d271073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212297 q = 1) (hb : d271068 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212297, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87826 q ha hb
    | true =>
      simp only [d212297, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212298 q = 1) (hb : d271069 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212298, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212298, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212299 q = 1) (hb : d271070 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212299, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212299, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212300 q = 1) (hb : d271071 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212300, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212300, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212301 q = 1) (hb : d271072 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212301, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212301, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212302 q = 1) (hb : d271073 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212302, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212302, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87828 (p : Pattern) (ha : d212308 p = 1) (hb : d271079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212303 q = 1) (hb : d271074 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212303, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87827 q ha hb
    | true =>
      simp only [d212303, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d212304 q = 1) (hb : d271075 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212304, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212304, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d212305 q = 1) (hb : d271076 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212305, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212305, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d212306 q = 1) (hb : d271077 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212306, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212306, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d212307 q = 1) (hb : d271078 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212307, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212307, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d212308 q = 1) (hb : d271079 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212308, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212308, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro87829 (p : Pattern) (ha : d36090 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36086 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36086, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36087 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36087, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36088 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36088, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36089 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36089, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36090 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87830 (p : Pattern) (ha : d36097 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36086 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36086, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36087 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36087, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36088 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36088, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36089 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36093 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36093, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36094 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36094, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36095 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36095, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36096 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36096, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36097 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36097, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87831 (p : Pattern) (ha : d128207 p = 1) (hb : d270853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36093, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36094 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36095 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36096 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d270853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d270853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87832 (p : Pattern) (ha : d128217 p = 1) (hb : d270863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36069 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d270859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d270859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d270860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d270860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d270861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d270861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d270862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d270862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d270863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d270863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87833 (p : Pattern) (ha : d128223 p = 1) (hb : d270869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87829 q ha hb
    | true =>
      simp only [d36098, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87830 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36099 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d270851 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d270851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d270852 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d270852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d270854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d270854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87831 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d270855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d270855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d270856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d270856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d270857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d270857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d270858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d270858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d270864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d270864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87832 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d270865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d270865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d270866 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d270866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d270867 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d270867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d270868 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d270868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d270869 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d270869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87834 (p : Pattern) (ha : d128229 p = 1) (hb : d270875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d270870 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d270870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87833 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d270871 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d270871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d270872 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d270872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d270873 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d270873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d270874 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d270874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d270875 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d270875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro87835 (p : Pattern) (ha : d36302 p = 1) (hb : d128234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36297 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36298 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36298, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36299 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36299, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36300 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36300, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36301 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36301, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36302 q = 1) (hb : d128234 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87836 (p : Pattern) (ha : d36312 p = 1) (hb : d128239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36298 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36298, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36299 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36299, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36300 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36300, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36301 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36307 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36308 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36308, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36309 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36309, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36310 q = 1) (hb : d128237 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36310, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36311 q = 1) (hb : d128238 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36311, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36312 q = 1) (hb : d128239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36312, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87837 (p : Pattern) (ha : d128246 p = 1) (hb : d270878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36307 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36308 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36308, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36309 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36309, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36310 q = 1) (hb : d128244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36311 q = 1) (hb : d128245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d270878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d270878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87838 (p : Pattern) (ha : d128256 p = 1) (hb : d270889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128252 q = 1) (hb : d270885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d270885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d270886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128253, d270886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d270887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d270887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d270888 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d270888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d270889 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d270889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87839 (p : Pattern) (ha : d128262 p = 1) (hb : d270895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d128240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87835 q ha hb
    | true =>
      simp only [d36313, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87836 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36314 q = 1) (hb : d128241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128242 q = 1) (hb : d270876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128242, d270876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128243 q = 1) (hb : d270877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128243, d270877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128247 q = 1) (hb : d270879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128247, d270879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87837 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128248 q = 1) (hb : d270880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128248, d270880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128249 q = 1) (hb : d270881 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128249, d270881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128250 q = 1) (hb : d270882 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128250, d270882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128251 q = 1) (hb : d270883 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128251, d270883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128257 q = 1) (hb : d270890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128257, d270890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87838 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128258 q = 1) (hb : d270891 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128258, d270891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128259 q = 1) (hb : d270892 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128259, d270892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128260 q = 1) (hb : d270893 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128260, d270893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128261 q = 1) (hb : d270894 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128261, d270894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128262 q = 1) (hb : d270895 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128262, d270895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87840 (p : Pattern) (ha : d128268 p = 1) (hb : d270901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d270896 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d270896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87839 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d270897 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d270897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d270898 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d270898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d270899 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d270899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d270900 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d270900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d270901 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d270901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87841 (p : Pattern) (ha : d36634 p = 1) (hb : d128274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d36629 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36630 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36630, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36631 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36631, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36632 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36632, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36633 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36633, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36634 q = 1) (hb : d128274 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87842 (p : Pattern) (ha : d36644 p = 1) (hb : d128279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36629 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36630 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36630, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36631 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36631, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36632 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36632, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36633 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16325 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d36639 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36640 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36640, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36641 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36641, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36642 q = 1) (hb : d128277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36642, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36643 q = 1) (hb : d128278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36643, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d36644 q = 1) (hb : d128279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36644, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87843 (p : Pattern) (ha : d128286 p = 1) (hb : d270905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d36639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36640 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36640, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36641 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36641, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36642 q = 1) (hb : d128284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36643 q = 1) (hb : d128285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d270905 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d270905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87844 (p : Pattern) (ha : d128296 p = 1) (hb : d270916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128292 q = 1) (hb : d270912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d270912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d270913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128293, d270913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d270914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d270914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d270915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d270915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d270916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d270916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87845 (p : Pattern) (ha : d128302 p = 1) (hb : d270922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d128280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87841 q ha hb
    | true =>
      simp only [d36645, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87842 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36646 q = 1) (hb : d128281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128282 q = 1) (hb : d270903 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128282, d270903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128283 q = 1) (hb : d270904 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128283, d270904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128287 q = 1) (hb : d270906 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128287, d270906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87843 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128288 q = 1) (hb : d270907 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128288, d270907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128289 q = 1) (hb : d270908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128289, d270908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128290 q = 1) (hb : d270909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128290, d270909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128291 q = 1) (hb : d270910 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128291, d270910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128297 q = 1) (hb : d270917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128297, d270917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87844 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128298 q = 1) (hb : d270918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128298, d270918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128299 q = 1) (hb : d270919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128299, d270919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128300 q = 1) (hb : d270920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128300, d270920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128301 q = 1) (hb : d270921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128301, d270921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128302 q = 1) (hb : d270922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128302, d270922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87846 (p : Pattern) (ha : d128308 p = 1) (hb : d270928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d270923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d270923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87845 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d270924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d270924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d270925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d270925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d270926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d270926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d270927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d270927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d270928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d270928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87847 (p : Pattern) (ha : d37065 p = 1) (hb : d128315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37061 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37061, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d37062 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d37062, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37063 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37063, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d37064 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37064, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d37065 q = 1) (hb : d128315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37065, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37065, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87848 (p : Pattern) (ha : d37075 p = 1) (hb : d128320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37060 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d37061 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37061, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37061, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d37062 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37062, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d37062, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37063 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37063, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37063, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d37064 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37064, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37064, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d37070 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d37071 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d37071, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d37072 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d37072, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d37073 q = 1) (hb : d128318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d37073, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d37074 q = 1) (hb : d128319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d37074, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d37075 q = 1) (hb : d128320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d37075, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d37075, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87849 (p : Pattern) (ha : d128327 p = 1) (hb : d270933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37071 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37071, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d37072 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37072, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37073 q = 1) (hb : d128325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37074 q = 1) (hb : d128326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d270933 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d270933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro87850 (p : Pattern) (ha : d128337 p = 1) (hb : d270944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128333 q = 1) (hb : d270940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d270940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d270941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128334, d270941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d270942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d270942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d270943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d270943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d270944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d270944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87851 (p : Pattern) (ha : d128343 p = 1) (hb : d270950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d128321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87847 q ha hb
    | true =>
      simp only [d37076, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87848 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d37077 q = 1) (hb : d128322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128323 q = 1) (hb : d270931 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128323, d270931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128324 q = 1) (hb : d270932 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128324, d270932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128328 q = 1) (hb : d270934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128328, d270934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87849 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128329 q = 1) (hb : d270935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128329, d270935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128330 q = 1) (hb : d270936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128330, d270936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128331 q = 1) (hb : d270937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128331, d270937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128332 q = 1) (hb : d270938 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128332, d270938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128338 q = 1) (hb : d270945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128338, d270945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87850 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16772 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128339 q = 1) (hb : d270946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128339, d270946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128340 q = 1) (hb : d270947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128340, d270947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128341 q = 1) (hb : d270948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128341, d270948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128342 q = 1) (hb : d270949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128342, d270949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128343 q = 1) (hb : d270950 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128343, d270950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87852 (p : Pattern) (ha : d128349 p = 1) (hb : d270956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d270951 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d270951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87851 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d270952 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d270952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d270953 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d270953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d270954 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d270954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d270955 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d270955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d270956 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d270956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87853 (p : Pattern) (ha : d212313 p = 1) (hb : d270198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27677 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212309 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212309, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212309, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27807 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d212310 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212310, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212310, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d212311 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212311, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212311, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212312 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212312, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212312, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212313 q = 1) (hb : d270198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212313, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212313, d270198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87854 (p : Pattern) (ha : d212318 p = 1) (hb : d270208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27620 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d270193 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d212309 q = 1) (hb : d270194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212309, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212309, d270194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27807 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d212310 q = 1) (hb : d270195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212310, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212310, d270195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d212311 q = 1) (hb : d270196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212311, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212311, d270196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212312 q = 1) (hb : d270197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212312, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212312, d270197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27817 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27822 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27825 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d212314 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212314, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d212314, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212315 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212315, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212315, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212316 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212316, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d212316, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d212317 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212317, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d212317, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d212318 q = 1) (hb : d270208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212318, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d212318, d270208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87855 (p : Pattern) (ha : d212325 p = 1) (hb : d270962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212314 q = 1) (hb : d270204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212314, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212314, d270204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212315 q = 1) (hb : d270205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212315, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212315, d270205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212323 q = 1) (hb : d270206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212323, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212323, d270206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212324 q = 1) (hb : d270207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212324, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212324, d270207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212325 q = 1) (hb : d270962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212325, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212325, d270962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87856 (p : Pattern) (ha : d212335 p = 1) (hb : d270981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212331 q = 1) (hb : d270977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212331, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212331, d270977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28063 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212332 q = 1) (hb : d270978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212332, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212332, d270978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212333 q = 1) (hb : d270979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212333, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212333, d270979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212334 q = 1) (hb : d270980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212334, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212334, d270980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212335 q = 1) (hb : d270981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212335, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212335, d270981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87857 (p : Pattern) (ha : d212341 p = 1) (hb : d270987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212319 q = 1) (hb : d270209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212319, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87853 q ha hb
    | true =>
      simp only [d212319, d270209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87854 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27855 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212320 q = 1) (hb : d270210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212320, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212320, d270210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212321 q = 1) (hb : d270960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212321, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212321, d270960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212322 q = 1) (hb : d270961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212322, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212322, d270961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212326 q = 1) (hb : d270963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212326, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212326, d270963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87855 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d27864 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212327 q = 1) (hb : d270964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212327, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212327, d270964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212328 q = 1) (hb : d270965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212328, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212328, d270965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d212329 q = 1) (hb : d270966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212329, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212329, d270966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d212330 q = 1) (hb : d270967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212330, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212330, d270967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212336 q = 1) (hb : d270982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212336, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212336, d270982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87856 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28079 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212337 q = 1) (hb : d270983 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212337, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212337, d270983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212338 q = 1) (hb : d270984 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212338, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212338, d270984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d212339 q = 1) (hb : d270985 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212339, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212339, d270985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d212340 q = 1) (hb : d270986 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212340, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212340, d270986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d212341 q = 1) (hb : d270987 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212341, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212341, d270987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87858 (p : Pattern) (ha : d212347 p = 1) (hb : d270993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212342 q = 1) (hb : d270988 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212342, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212342, d270988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87857 q ha hb
  have h2 (q : Pattern) (ha : d212343 q = 1) (hb : d270989 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212343, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212343, d270989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212344 q = 1) (hb : d270990 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212344, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212344, d270990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212345 q = 1) (hb : d270991 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212345, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212345, d270991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212346 q = 1) (hb : d270992 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212346, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212346, d270992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212347 q = 1) (hb : d270993 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212347, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212347, d270993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87859 (p : Pattern) (ha : d212356 p = 1) (hb : d270553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28282 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212352 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212352, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d212352, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d28412 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d212353 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212353, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212353, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d212354 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212354, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212354, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212355 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212355, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212355, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212356 q = 1) (hb : d270553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212356, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212356, d270553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro87860 (p : Pattern) (ha : d212361 p = 1) (hb : d270563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28234 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28282 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d270548 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d212352 q = 1) (hb : d270549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212352, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212352, d270549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d28412 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d212353 q = 1) (hb : d270550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212353, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212353, d270550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d212354 q = 1) (hb : d270551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212354, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212354, d270551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212355 q = 1) (hb : d270552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212355, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212355, d270552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d28422 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d28427 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28430 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d212357 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212357, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d212357, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28437 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212358 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212358, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212358, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212359 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212359, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d212359, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d212360 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212360, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d212360, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d212361 q = 1) (hb : d270563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212361, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d212361, d270563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87861 (p : Pattern) (ha : d212368 p = 1) (hb : d271000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d270558 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212357 q = 1) (hb : d270559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212357, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212357, d270559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28437 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212358 q = 1) (hb : d270560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212358, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212358, d270560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212366 q = 1) (hb : d270561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212366, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212366, d270561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212367 q = 1) (hb : d270562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212367, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212367, d270562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212368 q = 1) (hb : d271000 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212368, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212368, d271000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87862 (p : Pattern) (ha : d212378 p = 1) (hb : d271019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212374 q = 1) (hb : d271015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212374, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212374, d271015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212375 q = 1) (hb : d271016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212375, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212375, d271016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d212376 q = 1) (hb : d271017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212376, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212376, d271017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212377 q = 1) (hb : d271018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212377, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212377, d271018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d212378 q = 1) (hb : d271019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212378, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212378, d271019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87863 (p : Pattern) (ha : d212384 p = 1) (hb : d271025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28226 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212362 q = 1) (hb : d270564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212362, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87859 q ha hb
    | true =>
      simp only [d212362, d270564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87860 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d212363 q = 1) (hb : d270565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212363, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212363, d270565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d212364 q = 1) (hb : d270998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212364, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212364, d270998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212365 q = 1) (hb : d270999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212365, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212365, d270999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212369 q = 1) (hb : d271001 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212369, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212369, d271001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87861 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d28469 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d212370 q = 1) (hb : d271002 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212370, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212370, d271002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d212371 q = 1) (hb : d271003 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212371, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212371, d271003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d212372 q = 1) (hb : d271004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212372, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212372, d271004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d212373 q = 1) (hb : d271005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212373, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212373, d271005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212379 q = 1) (hb : d271020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212379, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212379, d271020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87862 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28679 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d212380 q = 1) (hb : d271021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212380, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212380, d271021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d212381 q = 1) (hb : d271022 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212381, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212381, d271022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d212382 q = 1) (hb : d271023 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212382, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212382, d271023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d212383 q = 1) (hb : d271024 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212383, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212383, d271024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d212384 q = 1) (hb : d271025 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212384, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212384, d271025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87864 (p : Pattern) (ha : d212390 p = 1) (hb : d271031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212385 q = 1) (hb : d271026 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212385, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212385, d271026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87863 q ha hb
  have h2 (q : Pattern) (ha : d212386 q = 1) (hb : d271027 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212386, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212386, d271027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d212387 q = 1) (hb : d271028 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212387, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212387, d271028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d212388 q = 1) (hb : d271029 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212388, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212388, d271029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d212389 q = 1) (hb : d271030 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212389, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212389, d271030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d212390 q = 1) (hb : d271031 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212390, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d212390, d271031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87865 (p : Pattern) (ha : d212396 p = 1) (hb : d271037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d270902 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87834 q ha hb
    | true =>
      simp only [d128269, d270902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87840 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d270929 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d270929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87846 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d270930 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d270930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d270957 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d270957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87852 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d270958 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d270958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d270959 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d270959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d212348 q = 1) (hb : d270994 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212348, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212348, d270994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87858 q ha hb
  have h8 (q : Pattern) (ha : d212349 q = 1) (hb : d270995 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212349, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212349, d270995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d212350 q = 1) (hb : d270996 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212350, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212350, d270996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d212351 q = 1) (hb : d270997 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212351, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212351, d270997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d212391 q = 1) (hb : d271032 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212391, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212391, d271032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87864 q ha hb
  have h12 (q : Pattern) (ha : d212392 q = 1) (hb : d271033 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212392, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212392, d271033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d212393 q = 1) (hb : d271034 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212393, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212393, d271034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d212394 q = 1) (hb : d271035 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212394, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212394, d271035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d212395 q = 1) (hb : d271036 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212395, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212395, d271036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d212396 q = 1) (hb : d271037 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212396, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212396, d271037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro87866 (p : Pattern) (ha : d212402 p = 1) (hb : d271043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212397 q = 1) (hb : d271038 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212397, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87865 q ha hb
    | true =>
      simp only [d212397, d271038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212398 q = 1) (hb : d271039 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212398, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212398, d271039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212399 q = 1) (hb : d271040 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212399, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212399, d271040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212400 q = 1) (hb : d271041 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212400, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212400, d271041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212401 q = 1) (hb : d271042 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212401, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212401, d271042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212402 q = 1) (hb : d271043 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212402, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212402, d271043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87867 (p : Pattern) (ha : d212408 p = 1) (hb : d271049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212403 q = 1) (hb : d271044 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212403, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87866 q ha hb
    | true =>
      simp only [d212403, d271044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212404 q = 1) (hb : d271045 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212404, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212404, d271045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212405 q = 1) (hb : d271046 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212405, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212405, d271046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212406 q = 1) (hb : d271047 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212406, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212406, d271047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212407 q = 1) (hb : d271048 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212407, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212407, d271048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212408 q = 1) (hb : d271049 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212408, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212408, d271049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87868 (p : Pattern) (ha : d212414 p = 1) (hb : d271055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212409 q = 1) (hb : d271050 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212409, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87867 q ha hb
    | true =>
      simp only [d212409, d271050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212410 q = 1) (hb : d271051 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212410, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212410, d271051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212411 q = 1) (hb : d271052 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212411, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212411, d271052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212412 q = 1) (hb : d271053 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212412, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212412, d271053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212413 q = 1) (hb : d271054 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212413, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212413, d271054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212414 q = 1) (hb : d271055 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212414, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212414, d271055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87869 (p : Pattern) (ha : d212420 p = 1) (hb : d271061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212415 q = 1) (hb : d271056 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212415, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87868 q ha hb
    | true =>
      simp only [d212415, d271056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212416 q = 1) (hb : d271057 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212416, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212416, d271057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212417 q = 1) (hb : d271058 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212417, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212417, d271058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212418 q = 1) (hb : d271059 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212418, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212418, d271059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212419 q = 1) (hb : d271060 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212419, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212419, d271060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212420 q = 1) (hb : d271061 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212420, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212420, d271061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87870 (p : Pattern) (ha : d212426 p = 1) (hb : d271067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212421 q = 1) (hb : d271062 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212421, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87869 q ha hb
    | true =>
      simp only [d212421, d271062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212422 q = 1) (hb : d271063 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212422, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212422, d271063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212423 q = 1) (hb : d271064 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212423, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212423, d271064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212424 q = 1) (hb : d271065 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212424, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212424, d271065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212425 q = 1) (hb : d271066 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212425, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212425, d271066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212426 q = 1) (hb : d271067 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212426, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212426, d271067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87871 (p : Pattern) (ha : d212432 p = 1) (hb : d271073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212427 q = 1) (hb : d271068 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212427, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87870 q ha hb
    | true =>
      simp only [d212427, d271068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212428 q = 1) (hb : d271069 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212428, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212428, d271069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212429 q = 1) (hb : d271070 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212429, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212429, d271070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212430 q = 1) (hb : d271071 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212430, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212430, d271071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212431 q = 1) (hb : d271072 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212431, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212431, d271072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212432 q = 1) (hb : d271073 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212432, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212432, d271073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87872 (p : Pattern) (ha : d212438 p = 1) (hb : d271079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d212433 q = 1) (hb : d271074 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212433, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87871 q ha hb
    | true =>
      simp only [d212433, d271074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d212434 q = 1) (hb : d271075 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212434, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212434, d271075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d212435 q = 1) (hb : d271076 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212435, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212435, d271076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d212436 q = 1) (hb : d271077 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212436, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212436, d271077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d212437 q = 1) (hb : d271078 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212437, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212437, d271078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d212438 q = 1) (hb : d271079 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212438, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212438, d271079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87873 (p : Pattern) (ha : d36007 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36005 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36006 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d23 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h13 (q : Pattern) (ha : d36007 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro87874 (p : Pattern) (ha : d36013 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36008 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
    | true =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36009 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36010 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36011 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36012 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36013 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87875 (p : Pattern) (ha : d36019 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36014 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
    | true =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
  have h2 (q : Pattern) (ha : d36015 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36016 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36017 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36018 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36019 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro87876 (p : Pattern) (ha : d36025 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36023 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36024 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36025 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87877 (p : Pattern) (ha : d216471 p = 1) (hb : d269915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54027 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54028 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36026 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
    | true =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87878 (p : Pattern) (ha : d36032 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36023 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36024 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36032 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87879 (p : Pattern) (ha : d216471 p = 1) (hb : d269920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54027 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54028 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36026 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
    | true =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54031 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54032 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36033 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87878 q ha hb
    | true =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54007 q ha hb
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d269916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54007 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d216471 q = 1) (hb : d269917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d216471 q = 1) (hb : d269918 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d216471 q = 1) (hb : d269919 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d216471 q = 1) (hb : d269920 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro87880 (p : Pattern) (ha : d216471 p = 1) (hb : d269927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36033 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87878 q ha hb
    | true =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54007 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d269916 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54007 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269917 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d269926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87881 (p : Pattern) (ha : d36056 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36051 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
  have h2 (q : Pattern) (ha : d36008 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
    | true =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36052 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36009 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36053 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36054 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36055 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36056 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87882 (p : Pattern) (ha : d36062 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36057 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
    | true =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
  have h2 (q : Pattern) (ha : d36058 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36059 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36060 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36061 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36062 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro87883 (p : Pattern) (ha : d36068 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36063 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87882 q ha hb
    | true =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36064 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54011 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36065 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36066 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36067 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36068 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87884 (p : Pattern) (ha : d216471 p = 1) (hb : d269937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36069 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87883 q ha hb
    | true =>
      simp only [d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54012 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d269933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54012 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d269936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269937 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87885 (p : Pattern) (ha : d216471 p = 1) (hb : d269943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54015 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54015 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54016 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269921 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87877 q ha hb
    | true =>
      simp only [d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87879 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54017 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269922 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269923 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d216471 q = 1) (hb : d269924 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d216471 q = 1) (hb : d269928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87880 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269932 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d216471 q = 1) (hb : d269938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87884 q ha hb
  have h17 (q : Pattern) (ha : d216471 q = 1) (hb : d269939 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d216471 q = 1) (hb : d269940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d216471 q = 1) (hb : d269941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d216471 q = 1) (hb : d269942 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d216471 q = 1) (hb : d269943 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro87886 (p : Pattern) (ha : d36090 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36026 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
    | true =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
  have h2 (q : Pattern) (ha : d36086 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36087 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36088 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36089 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36090 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87887 (p : Pattern) (ha : d36097 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36026 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
    | true =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
  have h2 (q : Pattern) (ha : d36086 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36087 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36088 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36089 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36033 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87878 q ha hb
    | true =>
      simp only [d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54007 q ha hb
  have h7 (q : Pattern) (ha : d36093 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36094 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36095 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36096 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36097 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87888 (p : Pattern) (ha : d36201 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36026 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
    | true =>
      simp only [d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
  have h2 (q : Pattern) (ha : d36086 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36087 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36088 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36089 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54005 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36201 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87889 (p : Pattern) (ha : d36102 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36023 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36101 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36102 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87890 (p : Pattern) (ha : d36109 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36107 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36108 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36109 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87891 (p : Pattern) (ha : d36120 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36118 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36119 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36005 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36006 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d36120 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro87892 (p : Pattern) (ha : d36126 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9455 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9456 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h11 (q : Pattern) (ha : d22 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d23 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h13 (q : Pattern) (ha : d36126 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro87893 (p : Pattern) (ha : d36132 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36121 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
    | true =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36122 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36123 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36124 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36008 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
    | true =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36009 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36010 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36011 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36125 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36129 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36130 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36131 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36132 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87894 (p : Pattern) (ha : d36138 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36133 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87893 q ha hb
    | true =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
  have h2 (q : Pattern) (ha : d36134 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36135 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36014 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
    | true =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
  have h5 (q : Pattern) (ha : d36015 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36016 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36136 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36017 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36137 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36138 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro87895 (p : Pattern) (ha : d36144 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36139 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87894 q ha hb
    | true =>
      simp only [d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36140 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36141 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36142 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36143 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36144 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87896 (p : Pattern) (ha : d36172 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36169 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36170 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36171 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36172 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87897 (p : Pattern) (ha : d216471 p = 1) (hb : d269953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36103 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87889 q ha hb
    | true =>
      simp only [d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54027 q ha hb
  have h2 (q : Pattern) (ha : d36104 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36105 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36106 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36110 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87890 q ha hb
    | true =>
      simp only [d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54028 q ha hb
  have h6 (q : Pattern) (ha : d36111 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36112 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36145 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87895 q ha hb
    | true =>
      simp only [d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36173 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87896 q ha hb
    | true =>
      simp only [d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36174 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269953 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87898 (p : Pattern) (ha : d36179 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36023 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36101 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36179 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87899 (p : Pattern) (ha : d36184 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54004 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36022 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36107 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36108 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36184 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87900 (p : Pattern) (ha : d36188 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36139 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87894 q ha hb
    | true =>
      simp only [d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36140 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36141 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36142 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36143 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36188 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87901 (p : Pattern) (ha : d36193 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87875 q ha hb
    | true =>
      simp only [d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36169 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36170 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36171 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36193 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87902 (p : Pattern) (ha : d216471 p = 1) (hb : d269958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36103 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87889 q ha hb
    | true =>
      simp only [d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54027 q ha hb
  have h2 (q : Pattern) (ha : d36104 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36105 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36106 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36110 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87890 q ha hb
    | true =>
      simp only [d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54028 q ha hb
  have h6 (q : Pattern) (ha : d36111 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36112 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36145 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87895 q ha hb
    | true =>
      simp only [d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87876 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269949 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36173 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87896 q ha hb
    | true =>
      simp only [d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36174 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269950 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269951 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269952 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36180 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87898 q ha hb
    | true =>
      simp only [d36180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54031 q ha hb
  have h16 (q : Pattern) (ha : d36181 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36182 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36183 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36185 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87899 q ha hb
    | true =>
      simp only [d36185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54032 q ha hb
  have h20 (q : Pattern) (ha : d36186 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d36187 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36189 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87900 q ha hb
    | true =>
      simp only [d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87878 q ha hb
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d269954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d36194 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87901 q ha hb
    | true =>
      simp only [d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d36195 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d216471 q = 1) (hb : d269955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d216471 q = 1) (hb : d269956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d216471 q = 1) (hb : d269957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d216471 q = 1) (hb : d269958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro87903 (p : Pattern) (ha : d216471 p = 1) (hb : d269965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36189 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87900 q ha hb
    | true =>
      simp only [d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87878 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d269954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d36194 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87901 q ha hb
    | true =>
      simp only [d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36195 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d269964 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269965 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87904 (p : Pattern) (ha : d36224 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36214 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
  have h2 (q : Pattern) (ha : d36121 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
    | true =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36215 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36122 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36216 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36217 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36051 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
  have h8 (q : Pattern) (ha : d36008 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87873 q ha hb
    | true =>
      simp only [d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36052 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36009 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36053 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36054 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36218 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36219 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
  have h15 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36220 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36221 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36222 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36223 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d36224 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro87905 (p : Pattern) (ha : d36230 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36225 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87904 q ha hb
    | true =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
  have h2 (q : Pattern) (ha : d36226 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36227 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36057 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
    | true =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
  have h5 (q : Pattern) (ha : d36058 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36059 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36228 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36060 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36229 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36230 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro87906 (p : Pattern) (ha : d36236 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36231 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87905 q ha hb
    | true =>
      simp only [d36231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36232 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36063 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87882 q ha hb
    | true =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36064 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36233 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36234 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36235 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36236 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87907 (p : Pattern) (ha : d36261 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36063 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87882 q ha hb
    | true =>
      simp only [d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36064 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36258 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36259 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36260 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36261 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87908 (p : Pattern) (ha : d216471 p = 1) (hb : d269975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36237 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87906 q ha hb
    | true =>
      simp only [d36237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87883 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d269971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d36262 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87907 q ha hb
    | true =>
      simp only [d36262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36263 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d269974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87909 (p : Pattern) (ha : d216471 p = 1) (hb : d269981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36091 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87886 q ha hb
  have h2 (q : Pattern) (ha : d36092 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36098 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87886 q ha hb
    | true =>
      simp only [d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87887 q ha hb
  have h4 (q : Pattern) (ha : d36099 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36100 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d36100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87897 q ha hb
    | true =>
      simp only [d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87902 q ha hb
  have h7 (q : Pattern) (ha : d36202 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87888 q ha hb
    | true =>
      simp only [d36202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54016 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d216471 q = 1) (hb : d269962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d269962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d216471 q = 1) (hb : d269966 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87903 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54038 q ha hb
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269967 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269968 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269969 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d216471 q = 1) (hb : d269970 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d216471 q = 1) (hb : d269976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87908 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54039 q ha hb
  have h19 (q : Pattern) (ha : d216471 q = 1) (hb : d269977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d216471 q = 1) (hb : d269978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d269978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d216471 q = 1) (hb : d269979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d216471 q = 1) (hb : d269980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d269981 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro87910 (p : Pattern) (ha : d216471 p = 1) (hb : d269987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54014 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87885 q ha hb
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d269946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d216471 q = 1) (hb : d269982 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87909 q ha hb
  have h11 (q : Pattern) (ha : d216471 q = 1) (hb : d269983 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269984 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269985 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269986 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269987 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87911 (p : Pattern) (ha : d36282 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36133 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87893 q ha hb
    | true =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
  have h2 (q : Pattern) (ha : d36134 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36135 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36014 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
    | true =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
  have h5 (q : Pattern) (ha : d36015 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36016 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36136 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36280 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36281 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36282 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro87912 (p : Pattern) (ha : d36286 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36014 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
    | true =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
  have h2 (q : Pattern) (ha : d36015 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36016 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36280 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36285 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36286 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87913 (p : Pattern) (ha : d36292 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36291 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36292 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87914 (p : Pattern) (ha : d36296 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36295 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36296 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87915 (p : Pattern) (ha : d36302 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87913 q ha hb
    | true =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87914 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36302 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87916 (p : Pattern) (ha : d36305 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36291 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36305 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87917 (p : Pattern) (ha : d36306 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36295 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36306 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87918 (p : Pattern) (ha : d36312 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87913 q ha hb
    | true =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87914 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36307 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87916 q ha hb
    | true =>
      simp only [d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87917 q ha hb
  have h7 (q : Pattern) (ha : d36308 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36309 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36310 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36311 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36312 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87919 (p : Pattern) (ha : d36460 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87913 q ha hb
    | true =>
      simp only [d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87914 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36455 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87914 q ha hb
    | true =>
      simp only [d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36456 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36457 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36458 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36459 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36460 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87920 (p : Pattern) (ha : d36466 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36455 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87914 q ha hb
    | true =>
      simp only [d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36456 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36457 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36458 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36459 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36461 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87917 q ha hb
    | true =>
      simp only [d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36462 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36463 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36464 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36465 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36466 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87921 (p : Pattern) (ha : d36475 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36461 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87917 q ha hb
    | true =>
      simp only [d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36462 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36463 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36464 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36465 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36475 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87922 (p : Pattern) (ha : d36518 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36057 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
    | true =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
  have h2 (q : Pattern) (ha : d36058 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36059 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36508 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36517 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36518 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87923 (p : Pattern) (ha : d36574 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36519 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87922 q ha hb
    | true =>
      simp only [d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36520 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36571 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36572 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36573 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36574 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87924 (p : Pattern) (ha : d36580 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36575 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87923 q ha hb
    | true =>
      simp only [d36575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36576 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36577 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36578 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36579 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36580 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87925 (p : Pattern) (ha : d36317 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36316 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36317 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87926 (p : Pattern) (ha : d36319 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36318 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36319 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87927 (p : Pattern) (ha : d36326 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36324 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36325 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36326 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87928 (p : Pattern) (ha : d36329 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36327 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36328 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36329 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87929 (p : Pattern) (ha : d36340 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36336 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36337 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36338 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36339 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36118 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36119 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d36340 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro87930 (p : Pattern) (ha : d36345 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36118 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36119 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36119, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9455 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9456 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d36345 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87931 (p : Pattern) (ha : d36353 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36351 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d36352 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36352, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36352, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9455 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d9456 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9456, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h15 (q : Pattern) (ha : d36353 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87932 (p : Pattern) (ha : d36359 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36341 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
    | true =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36342 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36343 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36344 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36346 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
    | true =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36347 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36348 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36349 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36350 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36356 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36357 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36129 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36130 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36358 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36359 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87933 (p : Pattern) (ha : d36363 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36129 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36130 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36131 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36363 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87934 (p : Pattern) (ha : d36369 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36360 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87932 q ha hb
    | true =>
      simp only [d36360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87893 q ha hb
  have h2 (q : Pattern) (ha : d36361 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36362 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36364 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87893 q ha hb
    | true =>
      simp only [d36364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87933 q ha hb
  have h5 (q : Pattern) (ha : d36365 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36366 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36367 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36133 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87893 q ha hb
    | true =>
      simp only [d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
  have h9 (q : Pattern) (ha : d36134 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36135 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36014 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87874 q ha hb
    | true =>
      simp only [d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54003 q ha hb
  have h12 (q : Pattern) (ha : d36015 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36016 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36136 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36368 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36369 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro87935 (p : Pattern) (ha : d36375 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36370 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87934 q ha hb
    | true =>
      simp only [d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36371 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36372 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36373 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36374 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36375 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87936 (p : Pattern) (ha : d36423 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36420 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36421 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36422 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36423 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87937 (p : Pattern) (ha : d216471 p = 1) (hb : d269992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36320 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87925 q ha hb
    | true =>
      simp only [d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87926 q ha hb
  have h2 (q : Pattern) (ha : d36321 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36322 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36323 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36330 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87927 q ha hb
    | true =>
      simp only [d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87928 q ha hb
  have h6 (q : Pattern) (ha : d36331 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36332 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36376 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87935 q ha hb
    | true =>
      simp only [d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87913 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36424 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87936 q ha hb
    | true =>
      simp only [d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36425 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d269992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87938 (p : Pattern) (ha : d36430 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36316 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36430 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87939 (p : Pattern) (ha : d36431 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36318 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36431 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87940 (p : Pattern) (ha : d36436 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36324 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36325 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36436 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87941 (p : Pattern) (ha : d36437 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87912 q ha hb
    | true =>
      simp only [d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36327 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36328 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36437 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87942 (p : Pattern) (ha : d36441 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36370 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87934 q ha hb
    | true =>
      simp only [d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36371 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36372 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36373 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36374 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36441 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87943 (p : Pattern) (ha : d36447 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87911 q ha hb
    | true =>
      simp only [d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36420 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36421 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36422 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36447 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87944 (p : Pattern) (ha : d216471 p = 1) (hb : d269997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36320 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87925 q ha hb
    | true =>
      simp only [d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87926 q ha hb
  have h2 (q : Pattern) (ha : d36321 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36322 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36323 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36330 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87927 q ha hb
    | true =>
      simp only [d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87928 q ha hb
  have h6 (q : Pattern) (ha : d36331 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36332 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36376 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87935 q ha hb
    | true =>
      simp only [d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87913 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d269988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36424 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87936 q ha hb
    | true =>
      simp only [d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36425 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d269989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d269990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d269991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36432 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87938 q ha hb
    | true =>
      simp only [d36432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87939 q ha hb
  have h16 (q : Pattern) (ha : d36433 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36434 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36435 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36438 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87940 q ha hb
    | true =>
      simp only [d36438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87941 q ha hb
  have h20 (q : Pattern) (ha : d36439 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d36440 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36442 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87942 q ha hb
    | true =>
      simp only [d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87916 q ha hb
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d269993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d36448 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87943 q ha hb
    | true =>
      simp only [d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d36449 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d216471 q = 1) (hb : d269994 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d216471 q = 1) (hb : d269995 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d216471 q = 1) (hb : d269996 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d216471 q = 1) (hb : d269997 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro87945 (p : Pattern) (ha : d216471 p = 1) (hb : d270004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36442 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87942 q ha hb
    | true =>
      simp only [d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87916 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d269993 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d36448 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87943 q ha hb
    | true =>
      simp only [d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36449 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d269994 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d270002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d270003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d270004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87946 (p : Pattern) (ha : d36495 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36481 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
  have h2 (q : Pattern) (ha : d36341 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
    | true =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36482 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36342 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36483 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36484 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36485 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
  have h8 (q : Pattern) (ha : d36346 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
    | true =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36486 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36347 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36487 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36488 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36489 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36490 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
  have h15 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36491 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36492 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36493 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d36219 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
  have h21 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36220 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d36221 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d36222 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36494 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d36495 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro87947 (p : Pattern) (ha : d36499 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36219 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
  have h2 (q : Pattern) (ha : d36127 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87892 q ha hb
    | true =>
      simp only [d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36220 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36128 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36221 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36222 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54002 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36223 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36499 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87948 (p : Pattern) (ha : d36505 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36496 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87946 q ha hb
    | true =>
      simp only [d36496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87904 q ha hb
  have h2 (q : Pattern) (ha : d36497 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36498 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36500 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87904 q ha hb
    | true =>
      simp only [d36500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87947 q ha hb
  have h5 (q : Pattern) (ha : d36501 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36502 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36503 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36225 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87904 q ha hb
    | true =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
  have h9 (q : Pattern) (ha : d36226 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36227 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36057 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
    | true =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
  have h12 (q : Pattern) (ha : d36058 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36059 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36228 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36504 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36505 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro87949 (p : Pattern) (ha : d36510 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36225 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87904 q ha hb
    | true =>
      simp only [d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
  have h2 (q : Pattern) (ha : d36226 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36227 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36057 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87881 q ha hb
    | true =>
      simp only [d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54010 q ha hb
  have h5 (q : Pattern) (ha : d36058 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36059 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36228 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36508 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36509 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36510 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro87950 (p : Pattern) (ha : d36516 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36506 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87948 q ha hb
    | true =>
      simp only [d36506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36507 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36511 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87949 q ha hb
    | true =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36512 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36513 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36514 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36515 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36516 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87951 (p : Pattern) (ha : d36524 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36511 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87949 q ha hb
    | true =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36512 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36519 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87922 q ha hb
    | true =>
      simp only [d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36520 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36521 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36522 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36523 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36524 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87952 (p : Pattern) (ha : d36563 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36511 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87949 q ha hb
    | true =>
      simp only [d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36512 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36560 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36561 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36562 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36563 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87953 (p : Pattern) (ha : d216471 p = 1) (hb : d270014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36525 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87950 q ha hb
    | true =>
      simp only [d36525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87951 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d270010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d36564 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87952 q ha hb
    | true =>
      simp only [d36564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36565 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d270011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d270012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d270013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d270014 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87954 (p : Pattern) (ha : d216471 p = 1) (hb : d270020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36303 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87915 q ha hb
  have h2 (q : Pattern) (ha : d36304 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36313 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87915 q ha hb
    | true =>
      simp only [d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87918 q ha hb
  have h4 (q : Pattern) (ha : d36314 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36315 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d36315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d269998 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87937 q ha hb
    | true =>
      simp only [d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87944 q ha hb
  have h7 (q : Pattern) (ha : d36467 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87919 q ha hb
    | true =>
      simp only [d36467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87920 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d269999 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d270000 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d216471 q = 1) (hb : d270001 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d270001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d216471 q = 1) (hb : d270005 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87945 q ha hb
  have h12 (q : Pattern) (ha : d36476 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87921 q ha hb
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d270006 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d270007 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d270008 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d270008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d216471 q = 1) (hb : d270009 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d216471 q = 1) (hb : d270015 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87953 q ha hb
  have h18 (q : Pattern) (ha : d36581 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87924 q ha hb
  have h19 (q : Pattern) (ha : d216471 q = 1) (hb : d270016 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d216471 q = 1) (hb : d270017 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d270017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d216471 q = 1) (hb : d270018 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d270018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d216471 q = 1) (hb : d270019 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d270019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d270020 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro87955 (p : Pattern) (ha : d216471 p = 1) (hb : d270026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d216471 q = 1) (hb : d270021 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87954 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d270022 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d216471 q = 1) (hb : d270023 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d216471 q = 1) (hb : d270024 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d270025 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d270026 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87956 (p : Pattern) (ha : d36594 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d20, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9454 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36005 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36006 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36006, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36594 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro87957 (p : Pattern) (ha : d36600 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36341 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
    | true =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36342 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36343 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36344 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36346 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
    | true =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36347 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36348 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36349 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36350 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36356 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36357 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36597 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36598 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36599 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36600 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87958 (p : Pattern) (ha : d36603 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36121 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
    | true =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36122 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36123 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36124 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36597 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36598 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36601 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36602 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36603 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87959 (p : Pattern) (ha : d36607 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36597 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36598 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36602 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36607 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87960 (p : Pattern) (ha : d36614 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36604 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87957 q ha hb
    | true =>
      simp only [d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87958 q ha hb
  have h2 (q : Pattern) (ha : d36605 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36606 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36608 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87958 q ha hb
    | true =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87959 q ha hb
  have h5 (q : Pattern) (ha : d36609 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36610 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36611 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36612 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36613 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36614 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro87961 (p : Pattern) (ha : d36618 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36608 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87958 q ha hb
    | true =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87959 q ha hb
  have h2 (q : Pattern) (ha : d36609 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36610 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36612 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36617 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36618 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87962 (p : Pattern) (ha : d36624 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36623 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36624 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87963 (p : Pattern) (ha : d36628 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36627 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36628 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87964 (p : Pattern) (ha : d36634 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87962 q ha hb
    | true =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87963 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36634 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87965 (p : Pattern) (ha : d36637 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36623 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36637 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87966 (p : Pattern) (ha : d36638 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36627 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36638 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87967 (p : Pattern) (ha : d36644 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87962 q ha hb
    | true =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87963 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36639 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87965 q ha hb
    | true =>
      simp only [d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87966 q ha hb
  have h7 (q : Pattern) (ha : d36640 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36641 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36642 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36643 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36644 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87968 (p : Pattern) (ha : d36811 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87962 q ha hb
    | true =>
      simp only [d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87963 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36806 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87963 q ha hb
    | true =>
      simp only [d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36807 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36808 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36809 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36810 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36811 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87969 (p : Pattern) (ha : d36817 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36806 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87963 q ha hb
    | true =>
      simp only [d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36807 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36808 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36809 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36810 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36812 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87966 q ha hb
    | true =>
      simp only [d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36813 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36814 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36815 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36816 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36817 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87970 (p : Pattern) (ha : d36826 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36812 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87966 q ha hb
    | true =>
      simp only [d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36813 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36814 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36815 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36816 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36826 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87971 (p : Pattern) (ha : d36863 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36214 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
  have h2 (q : Pattern) (ha : d36121 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87891 q ha hb
    | true =>
      simp only [d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36215 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36122 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36216 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36217 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36847 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
  have h8 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36848 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36849 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36850 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36862 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36856 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36863 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87972 (p : Pattern) (ha : d36867 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36847 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
  have h2 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36848 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36849 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36850 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36856 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36867 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87973 (p : Pattern) (ha : d36886 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36868 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87971 q ha hb
    | true =>
      simp only [d36868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87972 q ha hb
  have h2 (q : Pattern) (ha : d36869 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36870 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36876 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36885 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36886 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87974 (p : Pattern) (ha : d36957 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36887 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87973 q ha hb
    | true =>
      simp only [d36887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36888 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36954 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36955 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36956 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36957 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87975 (p : Pattern) (ha : d36963 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36958 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87974 q ha hb
    | true =>
      simp only [d36958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36959 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36960 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36961 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36962 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36963 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87976 (p : Pattern) (ha : d36649 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36648 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36649 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87977 (p : Pattern) (ha : d36651 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36650 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36651 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87978 (p : Pattern) (ha : d36658 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36656 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36657 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36658 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87979 (p : Pattern) (ha : d36661 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36659 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36660 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36661 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87980 (p : Pattern) (ha : d36671 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36667 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36667, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36667, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36335 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36336 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36668 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d36337 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36669 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36670 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36670, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36670, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36338 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36339 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d36671 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro87981 (p : Pattern) (ha : d36676 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36336 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d36115 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36116 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d36116, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36337 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d36117 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36338 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36339 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36339, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9581 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9582 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d9582, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9583 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9584 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9585 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9585, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d36676 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro87982 (p : Pattern) (ha : d36685 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d36335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36336 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d36336, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d9582, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d36682 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36683 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d36684 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36684, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36684, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9452 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9453 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d9453, d216470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9583 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9584 q = 1) (hb : d216470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d9585 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9585, d216471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h15 (q : Pattern) (ha : d36685 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87983 (p : Pattern) (ha : d36691 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36672 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87980 q ha hb
    | true =>
      simp only [d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36673 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36674 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36675 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36677 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87981 q ha hb
    | true =>
      simp only [d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36678 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36679 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36680 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36681 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36686 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87982 q ha hb
    | true =>
      simp only [d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36687 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36688 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36689 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36356 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36357 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36690 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36691 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro87984 (p : Pattern) (ha : d36695 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36356 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36357 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36597 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36598 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36599 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36602 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36695 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro87985 (p : Pattern) (ha : d36701 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36692 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87983 q ha hb
    | true =>
      simp only [d36692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87957 q ha hb
  have h2 (q : Pattern) (ha : d36693 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36694 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36696 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87957 q ha hb
    | true =>
      simp only [d36696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87984 q ha hb
  have h5 (q : Pattern) (ha : d36697 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36698 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36699 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36604 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87957 q ha hb
    | true =>
      simp only [d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87958 q ha hb
  have h9 (q : Pattern) (ha : d36605 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36606 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36608 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87958 q ha hb
    | true =>
      simp only [d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87959 q ha hb
  have h12 (q : Pattern) (ha : d36609 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36610 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36611 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36700 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36701 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro87986 (p : Pattern) (ha : d36707 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36702 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87985 q ha hb
    | true =>
      simp only [d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36703 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36704 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36705 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36706 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36707 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87987 (p : Pattern) (ha : d36774 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36771 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36772 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36773 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36774 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro87988 (p : Pattern) (ha : d216471 p = 1) (hb : d270032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36652 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87976 q ha hb
    | true =>
      simp only [d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87977 q ha hb
  have h2 (q : Pattern) (ha : d36653 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36654 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36655 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36662 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87978 q ha hb
    | true =>
      simp only [d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87979 q ha hb
  have h6 (q : Pattern) (ha : d36663 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36664 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36708 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87986 q ha hb
    | true =>
      simp only [d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87962 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d270028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36775 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87987 q ha hb
    | true =>
      simp only [d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36776 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d270029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d270030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d270031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d216471 q = 1) (hb : d270032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro87989 (p : Pattern) (ha : d36781 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36648 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36781 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87990 (p : Pattern) (ha : d36782 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36650 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36782 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87991 (p : Pattern) (ha : d36787 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36656 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36657 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36787 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87992 (p : Pattern) (ha : d36788 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87961 q ha hb
    | true =>
      simp only [d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36659 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36660 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36788 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87993 (p : Pattern) (ha : d36792 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36702 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87985 q ha hb
    | true =>
      simp only [d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36703 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36704 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36705 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36706 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36792 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro87994 (p : Pattern) (ha : d36798 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87960 q ha hb
    | true =>
      simp only [d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36771 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36772 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36773 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36798 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro87995 (p : Pattern) (ha : d216471 p = 1) (hb : d270037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36652 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87976 q ha hb
    | true =>
      simp only [d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87977 q ha hb
  have h2 (q : Pattern) (ha : d36653 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36654 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36655 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36662 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87978 q ha hb
    | true =>
      simp only [d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87979 q ha hb
  have h6 (q : Pattern) (ha : d36663 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36664 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36708 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87986 q ha hb
    | true =>
      simp only [d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87962 q ha hb
  have h9 (q : Pattern) (ha : d216471 q = 1) (hb : d270028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d36775 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87987 q ha hb
    | true =>
      simp only [d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36776 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d216471 q = 1) (hb : d270029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d216471 q = 1) (hb : d270030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d216471 q = 1) (hb : d270031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36783 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87989 q ha hb
    | true =>
      simp only [d36783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87990 q ha hb
  have h16 (q : Pattern) (ha : d36784 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36785 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36786 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36789 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87991 q ha hb
    | true =>
      simp only [d36789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87992 q ha hb
  have h20 (q : Pattern) (ha : d36790 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d36791 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36793 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87993 q ha hb
    | true =>
      simp only [d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87965 q ha hb
  have h23 (q : Pattern) (ha : d216471 q = 1) (hb : d270033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d36799 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87994 q ha hb
    | true =>
      simp only [d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d36800 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d216471 q = 1) (hb : d270034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d216471 q = 1) (hb : d270035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d216471 q = 1) (hb : d270036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d216471 q = 1) (hb : d270037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro87996 (p : Pattern) (ha : d216471 p = 1) (hb : d270044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36793 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87993 q ha hb
    | true =>
      simp only [d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87965 q ha hb
  have h2 (q : Pattern) (ha : d216471 q = 1) (hb : d270033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d36799 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87994 q ha hb
    | true =>
      simp only [d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36800 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d216471 q = 1) (hb : d270034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d216471 q = 1) (hb : d270042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d216471 q = 1) (hb : d270043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d216471 q = 1) (hb : d270044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d270044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro87997 (p : Pattern) (ha : d36846 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36832 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87980 q ha hb
  have h2 (q : Pattern) (ha : d36672 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87980 q ha hb
    | true =>
      simp only [d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36833 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36673 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36834 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36835 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36836 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87981 q ha hb
  have h8 (q : Pattern) (ha : d36677 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87981 q ha hb
    | true =>
      simp only [d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36837 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36678 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36838 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36839 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36840 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36841 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87982 q ha hb
  have h15 (q : Pattern) (ha : d36686 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87982 q ha hb
    | true =>
      simp only [d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36842 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36687 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36843 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36844 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d36490 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
  have h21 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36491 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d36492 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d36493 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36845 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d36846 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro87998 (p : Pattern) (ha : d36852 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36481 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
  have h2 (q : Pattern) (ha : d36341 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87929 q ha hb
    | true =>
      simp only [d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36482 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36342 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36483 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36484 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36485 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
  have h8 (q : Pattern) (ha : d36346 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87930 q ha hb
    | true =>
      simp only [d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36486 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36347 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36487 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36488 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36489 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36490 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
  have h15 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36491 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36492 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36493 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d36847 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
  have h21 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36848 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d36849 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d36850 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36851 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d36852 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro87999 (p : Pattern) (ha : d36857 p = 1) (hb : d216471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36490 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
  have h2 (q : Pattern) (ha : d36354 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87931 q ha hb
    | true =>
      simp only [d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36491 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36355 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36492 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36493 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36847 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
  have h8 (q : Pattern) (ha : d36595 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro87956 q ha hb
    | true =>
      simp only [d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36848 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36596 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36849 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36850 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36851 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36856 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36857 q = 1) (hb : d216471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
