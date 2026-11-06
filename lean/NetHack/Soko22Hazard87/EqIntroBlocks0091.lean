import NetHack.Soko22Hazard87.EqIntroBlocks0090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro22750 (p : Pattern) (selected : d228859 p = 0) : d230333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228850 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22748 q selected
    | true =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228851 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228856 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228856, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228856, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228857 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228857, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228857, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228858 q = 0) : d230332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228858, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228858, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228859 q = 0) : d230333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228859, d230333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228859, d230333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22751 (p : Pattern) (selected : d228862 p = 0) : d230392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228716 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228717 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228723 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228724 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228725 q = 0) : d230305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228862 q = 0) : d230392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228862, d230392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228862, d230392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22752 (p : Pattern) (selected : d228868 p = 0) : d230398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228729 q = 0) : d230309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22722 q selected
    | true =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
  have h2 (q : Pattern) (selected : d228730 q = 0) : d230310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228731 q = 0) : d230311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228733 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
    | true =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22724 q selected
  have h5 (q : Pattern) (selected : d228734 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228735 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228736 q = 0) : d230316 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228863 q = 0) : d230393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228863, d230393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22751 q selected
    | true =>
      simp only [d228863, d230393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228864 q = 0) : d230394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228864, d230394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228864, d230394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228865 q = 0) : d230395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228865, d230395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228865, d230395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228866 q = 0) : d230396 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228866, d230396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228866, d230396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228867 q = 0) : d230397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228867, d230397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228867, d230397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228868 q = 0) : d230398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228868, d230398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228868, d230398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22753 (p : Pattern) (selected : d228874 p = 0) : d230404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228869 q = 0) : d230399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228869, d230399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22752 q selected
    | true =>
      simp only [d228869, d230399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228870 q = 0) : d230400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228870, d230400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228870, d230400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228871 q = 0) : d230401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228871, d230401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228871, d230401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228872 q = 0) : d230402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228872, d230402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228872, d230402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228873 q = 0) : d230403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228873, d230403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228873, d230403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228874 q = 0) : d230404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228874, d230404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228874, d230404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22754 (p : Pattern) (selected : d228880 p = 0) : d230410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228777 q = 0) : d230357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228777, d230357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22733 q selected
    | true =>
      simp only [d228777, d230357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22734 q selected
  have h2 (q : Pattern) (selected : d228778 q = 0) : d230358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228778, d230358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228778, d230358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228779 q = 0) : d230359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228779, d230359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228779, d230359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228780 q = 0) : d230360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228780, d230360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228780, d230360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228787 q = 0) : d230367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228787, d230367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22735 q selected
    | true =>
      simp only [d228787, d230367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22736 q selected
  have h6 (q : Pattern) (selected : d228788 q = 0) : d230368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228788, d230368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228788, d230368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228789 q = 0) : d230369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228789, d230369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228789, d230369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228810 q = 0) : d230390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228810, d230390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22740 q selected
    | true =>
      simp only [d228810, d230390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22727 q selected
  have h9 (q : Pattern) (selected : d228860 q = 0) : d230334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228860, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22749 q selected
    | true =>
      simp only [d228860, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22750 q selected
  have h10 (q : Pattern) (selected : d228861 q = 0) : d230391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228861, d230391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228861, d230391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228875 q = 0) : d230405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228875, d230405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22753 q selected
    | true =>
      simp only [d228875, d230405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228876 q = 0) : d230406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228876, d230406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228876, d230406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228877 q = 0) : d230407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228877, d230407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228877, d230407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228878 q = 0) : d230408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228878, d230408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228878, d230408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228879 q = 0) : d230409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228879, d230409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228879, d230409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228880 q = 0) : d230410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228880, d230410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228880, d230410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22755 (p : Pattern) (selected : d228881 p = 0) : d230411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228747 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228773 q = 0) : d230353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228773, d230353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228773, d230353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228881 q = 0) : d230411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228881, d230411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228881, d230411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22756 (p : Pattern) (selected : d228882 p = 0) : d230412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228751 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228775 q = 0) : d230355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228775, d230355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228775, d230355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228882 q = 0) : d230412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228882, d230412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228882, d230412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22757 (p : Pattern) (selected : d228887 p = 0) : d230417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228781 q = 0) : d230361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228781, d230361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228781, d230361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228782 q = 0) : d230362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228782, d230362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228782, d230362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228887 q = 0) : d230417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228887, d230417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228887, d230417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22758 (p : Pattern) (selected : d228888 p = 0) : d230418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228784 q = 0) : d230364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228784, d230364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228784, d230364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228785 q = 0) : d230365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228785, d230365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228785, d230365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228888 q = 0) : d230418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228888, d230418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228888, d230418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22759 (p : Pattern) (selected : d228892 p = 0) : d230422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228804 q = 0) : d230384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228804, d230384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22739 q selected
    | true =>
      simp only [d228804, d230384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228805 q = 0) : d230385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228805, d230385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228805, d230385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228806 q = 0) : d230386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228806, d230386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228806, d230386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228807 q = 0) : d230387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228807, d230387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228807, d230387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228808 q = 0) : d230388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228808, d230388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228808, d230388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228892 q = 0) : d230422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228892, d230422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228892, d230422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22760 (p : Pattern) (selected : d228894 p = 0) : d230342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228846 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228846, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22747 q selected
    | true =>
      simp only [d228846, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228847 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228847, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228847, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228850 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22748 q selected
    | true =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228851 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228852 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228852, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228852, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228853 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228853, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228853, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228854 q = 0) : d230328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228854, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228854, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228894 q = 0) : d230342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228894, d230342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228894, d230342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22761 (p : Pattern) (selected : d228895 p = 0) : d230343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228850 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22748 q selected
    | true =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228851 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228856 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228856, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228856, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228857 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228857, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228857, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228858 q = 0) : d230332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228858, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228858, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228895 q = 0) : d230343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228895, d230343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228895, d230343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22762 (p : Pattern) (selected : d228898 p = 0) : d230425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228869 q = 0) : d230399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228869, d230399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22752 q selected
    | true =>
      simp only [d228869, d230399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228870 q = 0) : d230400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228870, d230400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228870, d230400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228871 q = 0) : d230401 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228871, d230401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228871, d230401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228872 q = 0) : d230402 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228872, d230402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228872, d230402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228873 q = 0) : d230403 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228873, d230403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228873, d230403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228898 q = 0) : d230425 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228898, d230425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228898, d230425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22763 (p : Pattern) (selected : d228904 p = 0) : d230431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228777 q = 0) : d230357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228777, d230357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22733 q selected
    | true =>
      simp only [d228777, d230357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22734 q selected
  have h2 (q : Pattern) (selected : d228778 q = 0) : d230358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228778, d230358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228778, d230358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228779 q = 0) : d230359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228779, d230359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228779, d230359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228780 q = 0) : d230360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228780, d230360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228780, d230360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228787 q = 0) : d230367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228787, d230367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22735 q selected
    | true =>
      simp only [d228787, d230367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22736 q selected
  have h6 (q : Pattern) (selected : d228788 q = 0) : d230368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228788, d230368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228788, d230368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228789 q = 0) : d230369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228789, d230369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228789, d230369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228810 q = 0) : d230390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228810, d230390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22740 q selected
    | true =>
      simp only [d228810, d230390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22727 q selected
  have h9 (q : Pattern) (selected : d228860 q = 0) : d230334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228860, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22749 q selected
    | true =>
      simp only [d228860, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22750 q selected
  have h10 (q : Pattern) (selected : d228861 q = 0) : d230391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228861, d230391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228861, d230391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228875 q = 0) : d230405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228875, d230405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22753 q selected
    | true =>
      simp only [d228875, d230405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228876 q = 0) : d230406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228876, d230406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228876, d230406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228877 q = 0) : d230407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228877, d230407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228877, d230407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228878 q = 0) : d230408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228878, d230408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228878, d230408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228879 q = 0) : d230409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228879, d230409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228879, d230409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228883 q = 0) : d230413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228883, d230413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22755 q selected
    | true =>
      simp only [d228883, d230413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22756 q selected
  have h17 (q : Pattern) (selected : d228884 q = 0) : d230414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228884, d230414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228884, d230414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228885 q = 0) : d230415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228885, d230415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228885, d230415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d228886 q = 0) : d230416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228886, d230416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228886, d230416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228889 q = 0) : d230419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228889, d230419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22757 q selected
    | true =>
      simp only [d228889, d230419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22758 q selected
  have h21 (q : Pattern) (selected : d228890 q = 0) : d230420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228890, d230420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228890, d230420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d228891 q = 0) : d230421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228891, d230421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228891, d230421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228893 q = 0) : d230423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228893, d230423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22759 q selected
    | true =>
      simp only [d228893, d230423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22730 q selected
  have h24 (q : Pattern) (selected : d228896 q = 0) : d230344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228896, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22760 q selected
    | true =>
      simp only [d228896, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22761 q selected
  have h25 (q : Pattern) (selected : d228897 q = 0) : d230424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228897, d230424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d228897, d230424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d228899 q = 0) : d230426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228899, d230426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22762 q selected
    | true =>
      simp only [d228899, d230426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d228900 q = 0) : d230427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228900, d230427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d228900, d230427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d228901 q = 0) : d230428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228901, d230428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d228901, d230428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d228902 q = 0) : d230429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228902, d230429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d228902, d230429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d228903 q = 0) : d230430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228903, d230430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228903, d230430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d228904 q = 0) : d230431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228904, d230431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228904, d230431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22764 (p : Pattern) (selected : d228911 p = 0) : d230438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228754 q = 0) : d230334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22727 q selected
    | true =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22728 q selected
  have h2 (q : Pattern) (selected : d228755 q = 0) : d230335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228756 q = 0) : d230336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228757 q = 0) : d230337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228758 q = 0) : d230338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228906 q = 0) : d230433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228906, d230433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22728 q selected
    | true =>
      simp only [d228906, d230433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228907 q = 0) : d230434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228907, d230434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228907, d230434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228908 q = 0) : d230435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228908, d230435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228908, d230435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228909 q = 0) : d230436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228909, d230436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228909, d230436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228910 q = 0) : d230437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228910, d230437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228910, d230437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228911 q = 0) : d230438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228911, d230438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228911, d230438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22765 (p : Pattern) (selected : d228917 p = 0) : d230444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228906 q = 0) : d230433 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228906, d230433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22728 q selected
    | true =>
      simp only [d228906, d230433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228907 q = 0) : d230434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228907, d230434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228907, d230434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228908 q = 0) : d230435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228908, d230435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228908, d230435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228909 q = 0) : d230436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228909, d230436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228909, d230436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228910 q = 0) : d230437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228910, d230437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228910, d230437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228912 q = 0) : d230439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228912, d230439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22731 q selected
    | true =>
      simp only [d228912, d230439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228913 q = 0) : d230440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228913, d230440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228913, d230440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228914 q = 0) : d230441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228914, d230441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228914, d230441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228915 q = 0) : d230442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228915, d230442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228915, d230442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228916 q = 0) : d230443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228916, d230443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228916, d230443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228917 q = 0) : d230444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228917, d230444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228917, d230444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22766 (p : Pattern) (selected : d228924 p = 0) : d230451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228893 q = 0) : d230423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228893, d230423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22759 q selected
    | true =>
      simp only [d228893, d230423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22730 q selected
  have h2 (q : Pattern) (selected : d228896 q = 0) : d230344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228896, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22760 q selected
    | true =>
      simp only [d228896, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22761 q selected
  have h3 (q : Pattern) (selected : d228897 q = 0) : d230424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228897, d230424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228897, d230424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228899 q = 0) : d230426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228899, d230426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22762 q selected
    | true =>
      simp only [d228899, d230426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228900 q = 0) : d230427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228900, d230427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228900, d230427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228901 q = 0) : d230428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228901, d230428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228901, d230428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228922 q = 0) : d230449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228922, d230449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228922, d230449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228923 q = 0) : d230450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228923, d230450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228923, d230450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228924 q = 0) : d230451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228924, d230451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228924, d230451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22767 (p : Pattern) (selected : d228926 p = 0) : d230453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228912 q = 0) : d230439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228912, d230439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22731 q selected
    | true =>
      simp only [d228912, d230439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228913 q = 0) : d230440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228913, d230440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228913, d230440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228914 q = 0) : d230441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228914, d230441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228914, d230441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228915 q = 0) : d230442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228915, d230442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228915, d230442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228916 q = 0) : d230443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228916, d230443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228916, d230443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228926 q = 0) : d230453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228926, d230453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228926, d230453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22768 (p : Pattern) (selected : d228946 p = 0) : d230473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228932 q = 0) : d230459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228932, d230459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228932, d230459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22737 q selected
  have h2 (q : Pattern) (selected : d228792 q = 0) : d230372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228792, d230372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22737 q selected
    | true =>
      simp only [d228792, d230372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228933 q = 0) : d230460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228933, d230460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228933, d230460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228793 q = 0) : d230373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228793, d230373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228793, d230373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228934 q = 0) : d230461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228934, d230461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228934, d230461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228935 q = 0) : d230462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228935, d230462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228935, d230462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228936 q = 0) : d230463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228936, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228936, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
  have h8 (q : Pattern) (selected : d228708 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
    | true =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228937 q = 0) : d230464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228937, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228937, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228709 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228938 q = 0) : d230465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228938, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228938, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228939 q = 0) : d230466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228939, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228939, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228940 q = 0) : d230467 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228940, d230467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228940, d230467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228941 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
  have h15 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228942 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d228943 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d228944 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228945 q = 0) : d230472 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228945, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228945, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228946 q = 0) : d230473 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228946, d230473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228946, d230473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22769 (p : Pattern) (selected : d228952 p = 0) : d230479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228936 q = 0) : d230463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228936, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228936, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
  have h2 (q : Pattern) (selected : d228708 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
    | true =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228937 q = 0) : d230464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228937, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228937, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228709 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228938 q = 0) : d230465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228938, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228938, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228939 q = 0) : d230466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228939, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228939, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228941 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
  have h8 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228942 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228943 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228944 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228945 q = 0) : d230472 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228945, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228945, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228947 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
  have h15 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228948 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d228949 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d228950 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228951 q = 0) : d230478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228952 q = 0) : d230479 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228952, d230479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228952, d230479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22770 (p : Pattern) (selected : d228957 p = 0) : d230484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228941 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
  have h2 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228942 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228943 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228944 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228947 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
  have h8 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228948 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228949 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228950 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228951 q = 0) : d230478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228956 q = 0) : d230483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228956, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228956, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228957 q = 0) : d230484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228957, d230484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228957, d230484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22771 (p : Pattern) (selected : d228962 p = 0) : d230489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228947 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
  have h2 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228948 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228949 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228950 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228956 q = 0) : d230483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228956, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228956, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228962 q = 0) : d230489 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228962, d230489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228962, d230489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22772 (p : Pattern) (selected : d228968 p = 0) : d230495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228953 q = 0) : d230480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228953, d230480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22768 q selected
    | true =>
      simp only [d228953, d230480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22769 q selected
  have h2 (q : Pattern) (selected : d228954 q = 0) : d230481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228954, d230481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228954, d230481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228955 q = 0) : d230482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228955, d230482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228955, d230482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228958 q = 0) : d230485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22769 q selected
    | true =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
  have h5 (q : Pattern) (selected : d228959 q = 0) : d230486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228960 q = 0) : d230487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228961 q = 0) : d230488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228961, d230488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228961, d230488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228963 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
    | true =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22771 q selected
  have h9 (q : Pattern) (selected : d228964 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228965 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228966 q = 0) : d230493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228967 q = 0) : d230494 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228967, d230494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228967, d230494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228968 q = 0) : d230495 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228968, d230495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228968, d230495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22773 (p : Pattern) (selected : d228973 p = 0) : d230500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228958 q = 0) : d230485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22769 q selected
    | true =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
  have h2 (q : Pattern) (selected : d228959 q = 0) : d230486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228960 q = 0) : d230487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228963 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
    | true =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22771 q selected
  have h5 (q : Pattern) (selected : d228964 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228965 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228966 q = 0) : d230493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228971 q = 0) : d230498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228971, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228971, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228972 q = 0) : d230499 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228972, d230499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228972, d230499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228973 q = 0) : d230500 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228973, d230500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228973, d230500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22774 (p : Pattern) (selected : d228979 p = 0) : d230506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228969 q = 0) : d230496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228969, d230496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22772 q selected
    | true =>
      simp only [d228969, d230496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228970 q = 0) : d230497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228970, d230497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228970, d230497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228974 q = 0) : d230501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228974, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22773 q selected
    | true =>
      simp only [d228974, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228975 q = 0) : d230502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228975, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228975, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228976 q = 0) : d230503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228976, d230503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228976, d230503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228977 q = 0) : d230504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228977, d230504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228977, d230504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228978 q = 0) : d230505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228978, d230505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228978, d230505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228979 q = 0) : d230506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228979, d230506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228979, d230506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22775 (p : Pattern) (selected : d228981 p = 0) : d230508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228963 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
    | true =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22771 q selected
  have h2 (q : Pattern) (selected : d228964 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228965 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228971 q = 0) : d230498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228971, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228971, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228980 q = 0) : d230507 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228980, d230507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228980, d230507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228981 q = 0) : d230508 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228981, d230508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228981, d230508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22776 (p : Pattern) (selected : d228987 p = 0) : d230514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228974 q = 0) : d230501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228974, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22773 q selected
    | true =>
      simp only [d228974, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228975 q = 0) : d230502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228975, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228975, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228982 q = 0) : d230509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228982, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22775 q selected
    | true =>
      simp only [d228982, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228983 q = 0) : d230510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228983, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228983, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228984 q = 0) : d230511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228984, d230511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228984, d230511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228985 q = 0) : d230512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228985, d230512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228985, d230512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228986 q = 0) : d230513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228986, d230513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228986, d230513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228987 q = 0) : d230514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228987, d230514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228987, d230514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22777 (p : Pattern) (selected : d229003 p = 0) : d230479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228989 q = 0) : d230463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228989, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228989, d230463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22741 q selected
  have h2 (q : Pattern) (selected : d228814 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228814, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22741 q selected
    | true =>
      simp only [d228814, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228990 q = 0) : d230464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228990, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228990, d230464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228815 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228815, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228815, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228991 q = 0) : d230465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228991, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228991, d230465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228992 q = 0) : d230466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228992, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228992, d230466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228993 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228993, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228993, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
  have h8 (q : Pattern) (selected : d228820 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
    | true =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228994 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228994, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228994, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228821 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228995 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228995, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228995, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228996 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228996, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228996, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228997 q = 0) : d230472 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228997, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228997, d230472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228998 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
  have h15 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228999 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d229000 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d229001 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d229002 q = 0) : d230478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229002, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229002, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d229003 q = 0) : d230479 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229003, d230479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229003, d230479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22778 (p : Pattern) (selected : d229005 p = 0) : d230484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228993 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228993, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228993, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
  have h2 (q : Pattern) (selected : d228820 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
    | true =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228994 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228994, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228994, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228821 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228995 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228995, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228995, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228996 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228996, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228996, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228998 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
  have h8 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228999 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229000 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229001 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229002 q = 0) : d230478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229002, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229002, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229004 q = 0) : d230483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229004, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229004, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229005 q = 0) : d230484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229005, d230484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229005, d230484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22779 (p : Pattern) (selected : d229009 p = 0) : d230489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228998 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
  have h2 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228999 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228999, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229000 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229000, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229001 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229001, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229004 q = 0) : d230483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229004, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229004, d230483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229009 q = 0) : d230489 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229009, d230489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229009, d230489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22780 (p : Pattern) (selected : d229016 p = 0) : d230500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229006 q = 0) : d230485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229006, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22777 q selected
    | true =>
      simp only [d229006, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22778 q selected
  have h2 (q : Pattern) (selected : d229007 q = 0) : d230486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229007, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229007, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229008 q = 0) : d230487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229008, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229008, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229010 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229010, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22778 q selected
    | true =>
      simp only [d229010, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22779 q selected
  have h5 (q : Pattern) (selected : d229011 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229011, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229011, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229012 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229012, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229012, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229013 q = 0) : d230493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229013, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229013, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229014 q = 0) : d230498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229014, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229014, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229015 q = 0) : d230499 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229015, d230499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229015, d230499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229016 q = 0) : d230500 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229016, d230500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229016, d230500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22781 (p : Pattern) (selected : d229020 p = 0) : d230508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229010 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229010, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22778 q selected
    | true =>
      simp only [d229010, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22779 q selected
  have h2 (q : Pattern) (selected : d229011 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229011, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229011, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229012 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229012, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229012, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229014 q = 0) : d230498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229014, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229014, d230498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229019 q = 0) : d230507 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229019, d230507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229019, d230507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229020 q = 0) : d230508 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229020, d230508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229020, d230508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22782 (p : Pattern) (selected : d229026 p = 0) : d230514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229017 q = 0) : d230501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229017, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22780 q selected
    | true =>
      simp only [d229017, d230501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229018 q = 0) : d230502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229018, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229018, d230502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229021 q = 0) : d230509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229021, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22781 q selected
    | true =>
      simp only [d229021, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229022 q = 0) : d230510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229022, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229022, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229023 q = 0) : d230511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229023, d230511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229023, d230511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229024 q = 0) : d230512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229024, d230512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229024, d230512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229025 q = 0) : d230513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229025, d230513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229025, d230513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229026 q = 0) : d230514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229026, d230514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229026, d230514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22783 (p : Pattern) (selected : d229030 p = 0) : d230519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229021 q = 0) : d230509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229021, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22781 q selected
    | true =>
      simp only [d229021, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229022 q = 0) : d230510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229022, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229022, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229027 q = 0) : d230516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229027, d230516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229027, d230516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229028 q = 0) : d230517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229028, d230517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229028, d230517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229029 q = 0) : d230518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229029, d230518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229029, d230518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229030 q = 0) : d230519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229030, d230519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229030, d230519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22784 (p : Pattern) (selected : d229033 p = 0) : d230522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228941 q = 0) : d230468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228941, d230468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
  have h2 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228942 q = 0) : d230469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228942, d230469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228943 q = 0) : d230470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228943, d230470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228944 q = 0) : d230471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228944, d230471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228947 q = 0) : d230474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228947, d230474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
  have h8 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228948 q = 0) : d230475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228948, d230475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228949 q = 0) : d230476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228949, d230476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228950 q = 0) : d230477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228950, d230477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228951 q = 0) : d230478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228951, d230478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229033 q = 0) : d230522 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229033, d230522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229033, d230522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro22785 (p : Pattern) (selected : d229039 p = 0) : d230528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228958 q = 0) : d230485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22769 q selected
    | true =>
      simp only [d228958, d230485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
  have h2 (q : Pattern) (selected : d228959 q = 0) : d230486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228959, d230486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228960 q = 0) : d230487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228960, d230487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228963 q = 0) : d230490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22770 q selected
    | true =>
      simp only [d228963, d230490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22771 q selected
  have h5 (q : Pattern) (selected : d228964 q = 0) : d230491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228964, d230491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228965 q = 0) : d230492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228965, d230492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228966 q = 0) : d230493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228966, d230493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229034 q = 0) : d230523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229034, d230523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22784 q selected
    | true =>
      simp only [d229034, d230523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229035 q = 0) : d230524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229035, d230524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229035, d230524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229036 q = 0) : d230525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229036, d230525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229036, d230525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229037 q = 0) : d230526 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229037, d230526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229037, d230526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229038 q = 0) : d230527 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229038, d230527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229038, d230527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229039 q = 0) : d230528 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229039, d230528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229039, d230528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22786 (p : Pattern) (selected : d229045 p = 0) : d230534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229040 q = 0) : d230529 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229040, d230529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22785 q selected
    | true =>
      simp only [d229040, d230529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229041 q = 0) : d230530 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229041, d230530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229041, d230530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229042 q = 0) : d230531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229042, d230531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229042, d230531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229043 q = 0) : d230532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229043, d230532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229043, d230532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229044 q = 0) : d230533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229044, d230533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229044, d230533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229045 q = 0) : d230534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229045, d230534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229045, d230534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22787 (p : Pattern) (selected : d229051 p = 0) : d230540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228988 q = 0) : d230515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228988, d230515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22774 q selected
    | true =>
      simp only [d228988, d230515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22776 q selected
  have h2 (q : Pattern) (selected : d229031 q = 0) : d230520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229031, d230520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22782 q selected
    | true =>
      simp only [d229031, d230520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22783 q selected
  have h3 (q : Pattern) (selected : d229032 q = 0) : d230521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229032, d230521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229032, d230521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229046 q = 0) : d230535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229046, d230535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22786 q selected
    | true =>
      simp only [d229046, d230535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229047 q = 0) : d230536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229047, d230536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229047, d230536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229048 q = 0) : d230537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229048, d230537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229048, d230537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229049 q = 0) : d230538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229049, d230538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229049, d230538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229050 q = 0) : d230539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229050, d230539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229050, d230539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229051 q = 0) : d230540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229051, d230540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229051, d230540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22788 (p : Pattern) (selected : d229056 p = 0) : d230519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228982 q = 0) : d230509 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228982, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22775 q selected
    | true =>
      simp only [d228982, d230509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228983 q = 0) : d230510 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228983, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228983, d230510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229053 q = 0) : d230516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229053, d230516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229053, d230516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229054 q = 0) : d230517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229054, d230517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229054, d230517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229055 q = 0) : d230518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229055, d230518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229055, d230518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229056 q = 0) : d230519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229056, d230519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229056, d230519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22789 (p : Pattern) (selected : d229062 p = 0) : d230547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229057 q = 0) : d230542 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229057, d230542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22788 q selected
    | true =>
      simp only [d229057, d230542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229058 q = 0) : d230543 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229058, d230543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229058, d230543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229059 q = 0) : d230544 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229059, d230544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229059, d230544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229060 q = 0) : d230545 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229060, d230545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229060, d230545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229061 q = 0) : d230546 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229061, d230546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229061, d230546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229062 q = 0) : d230547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229062, d230547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229062, d230547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22790 (p : Pattern) (selected : d229068 p = 0) : d230553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228760 q = 0) : d230340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228760, d230340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228760, d230340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22729 q selected
  have h2 (q : Pattern) (selected : d228761 q = 0) : d230341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228761, d230341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228761, d230341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228770 q = 0) : d230350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228770, d230350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22729 q selected
    | true =>
      simp only [d228770, d230350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22732 q selected
  have h4 (q : Pattern) (selected : d228771 q = 0) : d230351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228771, d230351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228771, d230351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228772 q = 0) : d230352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228772, d230352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228772, d230352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228905 q = 0) : d230432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228905, d230432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22754 q selected
    | true =>
      simp only [d228905, d230432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22763 q selected
  have h7 (q : Pattern) (selected : d228918 q = 0) : d230445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228918, d230445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22764 q selected
    | true =>
      simp only [d228918, d230445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22765 q selected
  have h8 (q : Pattern) (selected : d228919 q = 0) : d230446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228919, d230446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228919, d230446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228920 q = 0) : d230447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228920, d230447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228920, d230447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d228921 q = 0) : d230448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228921, d230448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228921, d230448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228925 q = 0) : d230452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228925, d230452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228925, d230452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22766 q selected
  have h12 (q : Pattern) (selected : d228927 q = 0) : d230454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228927, d230454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228927, d230454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22767 q selected
  have h13 (q : Pattern) (selected : d228928 q = 0) : d230455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228928, d230455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228928, d230455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228929 q = 0) : d230456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228929, d230456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228929, d230456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228930 q = 0) : d230457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228930, d230457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228930, d230457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228931 q = 0) : d230458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228931, d230458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228931, d230458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229052 q = 0) : d230541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229052, d230541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229052, d230541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22787 q selected
  have h18 (q : Pattern) (selected : d229063 q = 0) : d230548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229063, d230548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229063, d230548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22789 q selected
  have h19 (q : Pattern) (selected : d229064 q = 0) : d230549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229064, d230549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d229064, d230549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d229065 q = 0) : d230550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229065, d230550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d229065, d230550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d229066 q = 0) : d230551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229066, d230551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d229066, d230551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d229067 q = 0) : d230552 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229067, d230552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d229067, d230552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d229068 q = 0) : d230553 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d229068, d230553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229068, d230553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22791 (p : Pattern) (selected : d229074 p = 0) : d230559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229069 q = 0) : d230554 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d229069, d230554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229069, d230554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22790 q selected
  have h2 (q : Pattern) (selected : d229070 q = 0) : d230555 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d229070, d230555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229070, d230555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229071 q = 0) : d230556 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d229071, d230556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229071, d230556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229072 q = 0) : d230557 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d229072, d230557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229072, d230557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229073 q = 0) : d230558 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d229073, d230558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229073, d230558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229074 q = 0) : d230559 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d229074, d230559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229074, d230559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22792 (p : Pattern) (selected : d229080 p = 0) : d230565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2031 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229079 q = 0) : d230564 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229079, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229079, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229080 q = 0) : d230565 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229080, d230565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229080, d230565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro22793 (p : Pattern) (selected : d229086 p = 0) : d230571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2031 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229079 q = 0) : d230564 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229079, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229079, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2049 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229085 q = 0) : d230570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229085, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229085, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229086 q = 0) : d230571 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229086, d230571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229086, d230571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22794 (p : Pattern) (selected : d229093 p = 0) : d230578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2049 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229085 q = 0) : d230570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229085, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229085, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2061 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229092 q = 0) : d230577 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229092, d230577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229092, d230577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229093 q = 0) : d230578 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229093, d230578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229093, d230578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22795 (p : Pattern) (selected : d229099 p = 0) : d230584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229081 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
    | true =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229082 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229083 q = 0) : d230568 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229083, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229083, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229084 q = 0) : d230569 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229084, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229084, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229089 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229090 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229091 q = 0) : d230576 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229091, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229091, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229096 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229097 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d229098 q = 0) : d230583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229099 q = 0) : d230584 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229099, d230584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229099, d230584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22796 (p : Pattern) (selected : d229101 p = 0) : d230586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229089 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229090 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229096 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229097 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229098 q = 0) : d230583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229100 q = 0) : d230585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229100, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229100, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229101 q = 0) : d230586 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229101, d230586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229101, d230586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22797 (p : Pattern) (selected : d229105 p = 0) : d230590 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229096 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229097 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229100 q = 0) : d230585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229100, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229100, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229105 q = 0) : d230590 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229105, d230590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229105, d230590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22798 (p : Pattern) (selected : d229112 p = 0) : d230597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229102 q = 0) : d230587 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22795 q selected
    | true =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
  have h2 (q : Pattern) (selected : d229103 q = 0) : d230588 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229104 q = 0) : d230589 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229106 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
    | true =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22797 q selected
  have h5 (q : Pattern) (selected : d229107 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229108 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229109 q = 0) : d230594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229110 q = 0) : d230595 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229110, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229110, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229111 q = 0) : d230596 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229111, d230596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229111, d230596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229112 q = 0) : d230597 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229112, d230597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229112, d230597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22799 (p : Pattern) (selected : d229116 p = 0) : d230601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229106 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
    | true =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22797 q selected
  have h2 (q : Pattern) (selected : d229107 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229108 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229110 q = 0) : d230595 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229110, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229110, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229115 q = 0) : d230600 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229115, d230600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229115, d230600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229116 q = 0) : d230601 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229116, d230601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229116, d230601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22800 (p : Pattern) (selected : d229122 p = 0) : d230607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229120 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229121 q = 0) : d230606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229121, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229121, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229122 q = 0) : d230607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229122, d230607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229122, d230607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22801 (p : Pattern) (selected : d229126 p = 0) : d230611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229124 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229125 q = 0) : d230610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229125, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229125, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229126 q = 0) : d230611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229126, d230611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229126, d230611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22802 (p : Pattern) (selected : d229132 p = 0) : d230617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229127 q = 0) : d230612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22800 q selected
    | true =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22801 q selected
  have h2 (q : Pattern) (selected : d229128 q = 0) : d230613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229129 q = 0) : d230614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229130 q = 0) : d230615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229131 q = 0) : d230616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229132 q = 0) : d230617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229132, d230617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229132, d230617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22803 (p : Pattern) (selected : d229135 p = 0) : d230620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229120 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229121 q = 0) : d230606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229121, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229121, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229135 q = 0) : d230620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229135, d230620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229135, d230620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22804 (p : Pattern) (selected : d229136 p = 0) : d230621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229124 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229125 q = 0) : d230610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229125, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229125, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229136 q = 0) : d230621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229136, d230621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229136, d230621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22805 (p : Pattern) (selected : d229142 p = 0) : d230627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229127 q = 0) : d230612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22800 q selected
    | true =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22801 q selected
  have h2 (q : Pattern) (selected : d229128 q = 0) : d230613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229129 q = 0) : d230614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229130 q = 0) : d230615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229131 q = 0) : d230616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229137 q = 0) : d230622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229137, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22803 q selected
    | true =>
      simp only [d229137, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22804 q selected
  have h7 (q : Pattern) (selected : d229138 q = 0) : d230623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229138, d230623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229138, d230623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229139 q = 0) : d230624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229139, d230624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229139, d230624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229140 q = 0) : d230625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229140, d230625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229140, d230625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229141 q = 0) : d230626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229141, d230626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229141, d230626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229142 q = 0) : d230627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229142, d230627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229142, d230627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22806 (p : Pattern) (selected : d229147 p = 0) : d230632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229120 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229146 q = 0) : d230631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229146, d230631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229146, d230631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229147 q = 0) : d230632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229147, d230632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229147, d230632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22807 (p : Pattern) (selected : d229149 p = 0) : d230634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229124 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229148 q = 0) : d230633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229148, d230633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229148, d230633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229149 q = 0) : d230634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229149, d230634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229149, d230634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22808 (p : Pattern) (selected : d229156 p = 0) : d230641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229154 q = 0) : d230639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229154, d230639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229154, d230639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229155 q = 0) : d230640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229155, d230640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229155, d230640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229156 q = 0) : d230641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229156, d230641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229156, d230641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22809 (p : Pattern) (selected : d229159 p = 0) : d230644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229157 q = 0) : d230642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229157, d230642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229157, d230642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229158 q = 0) : d230643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229158, d230643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229158, d230643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229159 q = 0) : d230644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229159, d230644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229159, d230644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22810 (p : Pattern) (selected : d229164 p = 0) : d230649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229081 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
    | true =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229082 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229083 q = 0) : d230568 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229083, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229083, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229084 q = 0) : d230569 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229084, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229084, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229163 q = 0) : d230648 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229163, d230648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229163, d230648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229089 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229090 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d229091 q = 0) : d230576 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229091, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229091, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229164 q = 0) : d230649 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229164, d230649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229164, d230649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22811 (p : Pattern) (selected : d229170 p = 0) : d230655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229165 q = 0) : d230650 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229165, d230650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22810 q selected
    | true =>
      simp only [d229165, d230650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22795 q selected
  have h2 (q : Pattern) (selected : d229166 q = 0) : d230651 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229166, d230651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229166, d230651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229167 q = 0) : d230652 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229167, d230652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229167, d230652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229102 q = 0) : d230587 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22795 q selected
    | true =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
  have h5 (q : Pattern) (selected : d229103 q = 0) : d230588 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229104 q = 0) : d230589 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229168 q = 0) : d230653 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229168, d230653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229168, d230653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229106 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
    | true =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22797 q selected
  have h9 (q : Pattern) (selected : d229107 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229108 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229109 q = 0) : d230594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229169 q = 0) : d230654 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229169, d230654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229169, d230654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229170 q = 0) : d230655 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229170, d230655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229170, d230655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22812 (p : Pattern) (selected : d229176 p = 0) : d230661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229171 q = 0) : d230656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229171, d230656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22811 q selected
    | true =>
      simp only [d229171, d230656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229172 q = 0) : d230657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229172, d230657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229172, d230657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229173 q = 0) : d230658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229173, d230658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229173, d230658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229174 q = 0) : d230659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229174, d230659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229174, d230659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229175 q = 0) : d230660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229175, d230660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229175, d230660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229176 q = 0) : d230661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229176, d230661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229176, d230661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22813 (p : Pattern) (selected : d229179 p = 0) : d230565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2197 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229178 q = 0) : d230564 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229178, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229178, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229179 q = 0) : d230565 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229179, d230565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229179, d230565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro22814 (p : Pattern) (selected : d229185 p = 0) : d230571 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2197 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229178 q = 0) : d230564 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229178, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229178, d230564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2215 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229184 q = 0) : d230570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229184, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229184, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229185 q = 0) : d230571 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229185, d230571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229185, d230571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22815 (p : Pattern) (selected : d229192 p = 0) : d230578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2215 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229184 q = 0) : d230570 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229184, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229184, d230570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2227 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229191 q = 0) : d230577 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229191, d230577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229191, d230577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229192 q = 0) : d230578 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229192, d230578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229192, d230578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22816 (p : Pattern) (selected : d229198 p = 0) : d230584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229180 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229180, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22813 q selected
    | true =>
      simp only [d229180, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229181 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229181, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229181, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229182 q = 0) : d230568 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229182, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229182, d230568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229183 q = 0) : d230569 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229183, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229183, d230569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229186 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
    | true =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229187 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229188 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229188, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229188, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229189 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229189, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229189, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229190 q = 0) : d230576 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229190, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229190, d230576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229195 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229196 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d229197 q = 0) : d230583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229197, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229197, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229198 q = 0) : d230584 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229198, d230584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229198, d230584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22817 (p : Pattern) (selected : d229200 p = 0) : d230586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229186 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
    | true =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229187 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229188 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229188, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229188, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229189 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229189, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229189, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229195 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229196 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229197 q = 0) : d230583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229197, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229197, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229199 q = 0) : d230585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229199, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229199, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229200 q = 0) : d230586 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229200, d230586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229200, d230586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22818 (p : Pattern) (selected : d229204 p = 0) : d230590 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229195 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229196 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229196, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229199 q = 0) : d230585 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229199, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229199, d230585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229204 q = 0) : d230590 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229204, d230590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229204, d230590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22819 (p : Pattern) (selected : d229211 p = 0) : d230597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229201 q = 0) : d230587 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229201, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22816 q selected
    | true =>
      simp only [d229201, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22817 q selected
  have h2 (q : Pattern) (selected : d229202 q = 0) : d230588 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229202, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229202, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229203 q = 0) : d230589 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229203, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229203, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229205 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229205, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22817 q selected
    | true =>
      simp only [d229205, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22818 q selected
  have h5 (q : Pattern) (selected : d229206 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229206, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229206, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229207 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229207, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229207, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229208 q = 0) : d230594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229208, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229208, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229209 q = 0) : d230595 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229209, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229209, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229210 q = 0) : d230596 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229210, d230596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229210, d230596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229211 q = 0) : d230597 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229211, d230597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229211, d230597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22820 (p : Pattern) (selected : d229215 p = 0) : d230601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229205 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229205, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22817 q selected
    | true =>
      simp only [d229205, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22818 q selected
  have h2 (q : Pattern) (selected : d229206 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229206, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229206, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229207 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229207, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229207, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229209 q = 0) : d230595 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229209, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229209, d230595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229214 q = 0) : d230600 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229214, d230600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229214, d230600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229215 q = 0) : d230601 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229215, d230601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229215, d230601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22821 (p : Pattern) (selected : d229221 p = 0) : d230607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229212 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229212, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22819 q selected
    | true =>
      simp only [d229212, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229213 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229213, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229213, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229216 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22820 q selected
    | true =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229217 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229218 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229218, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229218, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229219 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229219, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229219, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229220 q = 0) : d230606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229220, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229220, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229221 q = 0) : d230607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229221, d230607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229221, d230607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22822 (p : Pattern) (selected : d229225 p = 0) : d230611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229216 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22820 q selected
    | true =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229217 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229222 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229222, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229222, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229223 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229223, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229223, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229224 q = 0) : d230610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229224, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229224, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229225 q = 0) : d230611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229225, d230611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229225, d230611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22823 (p : Pattern) (selected : d229228 p = 0) : d230664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229089 q = 0) : d230574 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229089, d230574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229090 q = 0) : d230575 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229090, d230575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229096 q = 0) : d230581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229096, d230581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229097 q = 0) : d230582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229097, d230582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229098 q = 0) : d230583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229098, d230583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229228 q = 0) : d230664 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229228, d230664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229228, d230664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22824 (p : Pattern) (selected : d229234 p = 0) : d230670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229102 q = 0) : d230587 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22795 q selected
    | true =>
      simp only [d229102, d230587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
  have h2 (q : Pattern) (selected : d229103 q = 0) : d230588 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229103, d230588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229104 q = 0) : d230589 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229104, d230589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229106 q = 0) : d230591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22796 q selected
    | true =>
      simp only [d229106, d230591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22797 q selected
  have h5 (q : Pattern) (selected : d229107 q = 0) : d230592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229107, d230592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229108 q = 0) : d230593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229108, d230593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229109 q = 0) : d230594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229109, d230594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229229 q = 0) : d230665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229229, d230665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22823 q selected
    | true =>
      simp only [d229229, d230665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229230 q = 0) : d230666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229230, d230666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229230, d230666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229231 q = 0) : d230667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229231, d230667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229231, d230667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229232 q = 0) : d230668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229232, d230668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229232, d230668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229233 q = 0) : d230669 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229233, d230669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229233, d230669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229234 q = 0) : d230670 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229234, d230670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229234, d230670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22825 (p : Pattern) (selected : d229240 p = 0) : d230676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229235 q = 0) : d230671 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229235, d230671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22824 q selected
    | true =>
      simp only [d229235, d230671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229236 q = 0) : d230672 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229236, d230672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229236, d230672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229237 q = 0) : d230673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229237, d230673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229237, d230673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229238 q = 0) : d230674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229238, d230674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229238, d230674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229239 q = 0) : d230675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229239, d230675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229239, d230675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229240 q = 0) : d230676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229240, d230676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229240, d230676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22826 (p : Pattern) (selected : d229246 p = 0) : d230682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229150 q = 0) : d230635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229150, d230635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22806 q selected
    | true =>
      simp only [d229150, d230635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22807 q selected
  have h2 (q : Pattern) (selected : d229151 q = 0) : d230636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229151, d230636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229151, d230636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229152 q = 0) : d230637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229152, d230637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229152, d230637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229153 q = 0) : d230638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229153, d230638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229153, d230638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229160 q = 0) : d230645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229160, d230645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22808 q selected
    | true =>
      simp only [d229160, d230645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22809 q selected
  have h6 (q : Pattern) (selected : d229161 q = 0) : d230646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229161, d230646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229161, d230646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229162 q = 0) : d230647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229162, d230647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229162, d230647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229177 q = 0) : d230662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229177, d230662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22812 q selected
    | true =>
      simp only [d229177, d230662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22800 q selected
  have h9 (q : Pattern) (selected : d229226 q = 0) : d230612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229226, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22821 q selected
    | true =>
      simp only [d229226, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22822 q selected
  have h10 (q : Pattern) (selected : d229227 q = 0) : d230663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229227, d230663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229227, d230663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229241 q = 0) : d230677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229241, d230677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22825 q selected
    | true =>
      simp only [d229241, d230677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229242 q = 0) : d230678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229242, d230678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229242, d230678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229243 q = 0) : d230679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229243, d230679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229243, d230679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229244 q = 0) : d230680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229244, d230680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229244, d230680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229245 q = 0) : d230681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229245, d230681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229245, d230681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229246 q = 0) : d230682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229246, d230682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229246, d230682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22827 (p : Pattern) (selected : d229247 p = 0) : d230683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229120 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229120, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229146 q = 0) : d230631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229146, d230631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229146, d230631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229247 q = 0) : d230683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229247, d230683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229247, d230683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22828 (p : Pattern) (selected : d229248 p = 0) : d230684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229124 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229124, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229148 q = 0) : d230633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229148, d230633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229148, d230633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229248 q = 0) : d230684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229248, d230684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229248, d230684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22829 (p : Pattern) (selected : d229253 p = 0) : d230689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229119 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229119, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229154 q = 0) : d230639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229154, d230639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229154, d230639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229155 q = 0) : d230640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229155, d230640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229155, d230640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229253 q = 0) : d230689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229253, d230689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229253, d230689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22830 (p : Pattern) (selected : d229254 p = 0) : d230690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229117 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22799 q selected
    | true =>
      simp only [d229117, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229118 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229118, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229123 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229123, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229157 q = 0) : d230642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229157, d230642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229157, d230642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229158 q = 0) : d230643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229158, d230643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229158, d230643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229254 q = 0) : d230690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229254, d230690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229254, d230690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22831 (p : Pattern) (selected : d229258 p = 0) : d230694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229171 q = 0) : d230656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229171, d230656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22811 q selected
    | true =>
      simp only [d229171, d230656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229172 q = 0) : d230657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229172, d230657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229172, d230657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229113 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22798 q selected
    | true =>
      simp only [d229113, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229114 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229114, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229173 q = 0) : d230658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229173, d230658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229173, d230658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229174 q = 0) : d230659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229174, d230659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229174, d230659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229175 q = 0) : d230660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229175, d230660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229175, d230660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229258 q = 0) : d230694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229258, d230694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229258, d230694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22832 (p : Pattern) (selected : d229260 p = 0) : d230620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229212 q = 0) : d230598 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229212, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22819 q selected
    | true =>
      simp only [d229212, d230598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229213 q = 0) : d230599 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229213, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229213, d230599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229216 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22820 q selected
    | true =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229217 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229218 q = 0) : d230604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229218, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229218, d230604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229219 q = 0) : d230605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229219, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229219, d230605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229220 q = 0) : d230606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229220, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229220, d230606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229260 q = 0) : d230620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229260, d230620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229260, d230620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22833 (p : Pattern) (selected : d229261 p = 0) : d230621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229216 q = 0) : d230602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22820 q selected
    | true =>
      simp only [d229216, d230602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229217 q = 0) : d230603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, d230603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229222 q = 0) : d230608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229222, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229222, d230608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229223 q = 0) : d230609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229223, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229223, d230609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229224 q = 0) : d230610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229224, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229224, d230610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229261 q = 0) : d230621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229261, d230621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229261, d230621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22834 (p : Pattern) (selected : d229264 p = 0) : d230697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229235 q = 0) : d230671 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229235, d230671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22824 q selected
    | true =>
      simp only [d229235, d230671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229236 q = 0) : d230672 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229236, d230672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229236, d230672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229237 q = 0) : d230673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229237, d230673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229237, d230673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229238 q = 0) : d230674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229238, d230674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229238, d230674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229239 q = 0) : d230675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229239, d230675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229239, d230675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229264 q = 0) : d230697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229264, d230697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229264, d230697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22835 (p : Pattern) (selected : d229270 p = 0) : d230703 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229150 q = 0) : d230635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229150, d230635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22806 q selected
    | true =>
      simp only [d229150, d230635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22807 q selected
  have h2 (q : Pattern) (selected : d229151 q = 0) : d230636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229151, d230636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229151, d230636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229152 q = 0) : d230637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229152, d230637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229152, d230637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229153 q = 0) : d230638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229153, d230638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229153, d230638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229160 q = 0) : d230645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229160, d230645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22808 q selected
    | true =>
      simp only [d229160, d230645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22809 q selected
  have h6 (q : Pattern) (selected : d229161 q = 0) : d230646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229161, d230646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229161, d230646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229162 q = 0) : d230647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229162, d230647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229162, d230647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229177 q = 0) : d230662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229177, d230662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22812 q selected
    | true =>
      simp only [d229177, d230662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22800 q selected
  have h9 (q : Pattern) (selected : d229226 q = 0) : d230612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229226, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22821 q selected
    | true =>
      simp only [d229226, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22822 q selected
  have h10 (q : Pattern) (selected : d229227 q = 0) : d230663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229227, d230663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229227, d230663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229241 q = 0) : d230677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229241, d230677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22825 q selected
    | true =>
      simp only [d229241, d230677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229242 q = 0) : d230678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229242, d230678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229242, d230678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229243 q = 0) : d230679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229243, d230679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229243, d230679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229244 q = 0) : d230680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229244, d230680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229244, d230680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229245 q = 0) : d230681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229245, d230681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229245, d230681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229249 q = 0) : d230685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229249, d230685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22827 q selected
    | true =>
      simp only [d229249, d230685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22828 q selected
  have h17 (q : Pattern) (selected : d229250 q = 0) : d230686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229250, d230686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229250, d230686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d229251 q = 0) : d230687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229251, d230687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d229251, d230687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d229252 q = 0) : d230688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229252, d230688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229252, d230688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d229255 q = 0) : d230691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229255, d230691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22829 q selected
    | true =>
      simp only [d229255, d230691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22830 q selected
  have h21 (q : Pattern) (selected : d229256 q = 0) : d230692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229256, d230692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229256, d230692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d229257 q = 0) : d230693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229257, d230693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d229257, d230693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d229259 q = 0) : d230695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229259, d230695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22831 q selected
    | true =>
      simp only [d229259, d230695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22803 q selected
  have h24 (q : Pattern) (selected : d229262 q = 0) : d230622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229262, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22832 q selected
    | true =>
      simp only [d229262, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22833 q selected
  have h25 (q : Pattern) (selected : d229263 q = 0) : d230696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229263, d230696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d229263, d230696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d229265 q = 0) : d230698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229265, d230698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22834 q selected
    | true =>
      simp only [d229265, d230698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d229266 q = 0) : d230699 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229266, d230699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d229266, d230699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d229267 q = 0) : d230700 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229267, d230700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d229267, d230700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d229268 q = 0) : d230701 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229268, d230701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d229268, d230701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d229269 q = 0) : d230702 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229269, d230702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d229269, d230702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d229270 q = 0) : d230703 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229270, d230703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229270, d230703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22836 (p : Pattern) (selected : d229277 p = 0) : d230710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229127 q = 0) : d230612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22800 q selected
    | true =>
      simp only [d229127, d230612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22801 q selected
  have h2 (q : Pattern) (selected : d229128 q = 0) : d230613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229128, d230613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229129 q = 0) : d230614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229129, d230614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229130 q = 0) : d230615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229130, d230615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229131 q = 0) : d230616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229131, d230616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229272 q = 0) : d230705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229272, d230705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22801 q selected
    | true =>
      simp only [d229272, d230705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229273 q = 0) : d230706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229273, d230706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229273, d230706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229274 q = 0) : d230707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229274, d230707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229274, d230707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229275 q = 0) : d230708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229275, d230708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229275, d230708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229276 q = 0) : d230709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229276, d230709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229276, d230709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229277 q = 0) : d230710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229277, d230710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229277, d230710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22837 (p : Pattern) (selected : d229283 p = 0) : d230716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229272 q = 0) : d230705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229272, d230705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22801 q selected
    | true =>
      simp only [d229272, d230705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229273 q = 0) : d230706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229273, d230706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229273, d230706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229274 q = 0) : d230707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229274, d230707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229274, d230707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229275 q = 0) : d230708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229275, d230708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229275, d230708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229276 q = 0) : d230709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229276, d230709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229276, d230709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229278 q = 0) : d230711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229278, d230711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22804 q selected
    | true =>
      simp only [d229278, d230711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229279 q = 0) : d230712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229279, d230712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229279, d230712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229280 q = 0) : d230713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229280, d230713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229280, d230713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229281 q = 0) : d230714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229281, d230714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229281, d230714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229282 q = 0) : d230715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229282, d230715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229282, d230715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229283 q = 0) : d230716 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229283, d230716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229283, d230716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22838 (p : Pattern) (selected : d229290 p = 0) : d230723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229259 q = 0) : d230695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229259, d230695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22831 q selected
    | true =>
      simp only [d229259, d230695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22803 q selected
  have h2 (q : Pattern) (selected : d229262 q = 0) : d230622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229262, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22832 q selected
    | true =>
      simp only [d229262, d230622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22833 q selected
  have h3 (q : Pattern) (selected : d229263 q = 0) : d230696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229263, d230696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229263, d230696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229265 q = 0) : d230698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229265, d230698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22834 q selected
    | true =>
      simp only [d229265, d230698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229266 q = 0) : d230699 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229266, d230699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229266, d230699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229267 q = 0) : d230700 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229267, d230700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229267, d230700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229288 q = 0) : d230721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229288, d230721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229288, d230721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229289 q = 0) : d230722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229289, d230722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229289, d230722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229290 q = 0) : d230723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229290, d230723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229290, d230723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22839 (p : Pattern) (selected : d229292 p = 0) : d230725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229278 q = 0) : d230711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229278, d230711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22804 q selected
    | true =>
      simp only [d229278, d230711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229279 q = 0) : d230712 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229279, d230712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229279, d230712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229280 q = 0) : d230713 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229280, d230713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229280, d230713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229281 q = 0) : d230714 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229281, d230714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229281, d230714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229282 q = 0) : d230715 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229282, d230715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229282, d230715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229292 q = 0) : d230725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229292, d230725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229292, d230725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22840 (p : Pattern) (selected : d229308 p = 0) : d230741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229298 q = 0) : d230731 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229298, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229298, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
  have h2 (q : Pattern) (selected : d229081 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
    | true =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229299 q = 0) : d230732 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229299, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229299, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229082 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229300 q = 0) : d230733 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229300, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229300, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229301 q = 0) : d230734 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229301, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229301, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229302 q = 0) : d230735 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229302, d230735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229302, d230735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229303 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
  have h9 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d229304 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229305 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229306 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d229307 q = 0) : d230740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229307, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229307, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229308 q = 0) : d230741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229308, d230741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229308, d230741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22841 (p : Pattern) (selected : d229314 p = 0) : d230747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229298 q = 0) : d230731 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229298, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229298, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
  have h2 (q : Pattern) (selected : d229081 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22792 q selected
    | true =>
      simp only [d229081, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229299 q = 0) : d230732 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229299, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229299, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229082 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229082, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229300 q = 0) : d230733 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229300, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229300, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229301 q = 0) : d230734 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229301, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229301, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229303 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
  have h8 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229304 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229305 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229306 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229307 q = 0) : d230740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229307, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229307, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229309 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
  have h15 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d229310 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d229311 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d229312 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d229313 q = 0) : d230746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d229314 q = 0) : d230747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229314, d230747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229314, d230747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22842 (p : Pattern) (selected : d229319 p = 0) : d230752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229303 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
  have h2 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229304 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229305 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229306 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229309 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
  have h8 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229310 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229311 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229312 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229313 q = 0) : d230746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229318 q = 0) : d230751 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229318, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229318, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229319 q = 0) : d230752 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229319, d230752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229319, d230752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22843 (p : Pattern) (selected : d229324 p = 0) : d230757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229309 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
  have h2 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229310 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229311 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229312 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229318 q = 0) : d230751 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229318, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229318, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229324 q = 0) : d230757 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229324, d230757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229324, d230757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22844 (p : Pattern) (selected : d229330 p = 0) : d230763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229315 q = 0) : d230748 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229315, d230748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22840 q selected
    | true =>
      simp only [d229315, d230748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22841 q selected
  have h2 (q : Pattern) (selected : d229316 q = 0) : d230749 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229316, d230749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229316, d230749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229317 q = 0) : d230750 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229317, d230750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229317, d230750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229320 q = 0) : d230753 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22841 q selected
    | true =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
  have h5 (q : Pattern) (selected : d229321 q = 0) : d230754 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229322 q = 0) : d230755 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229323 q = 0) : d230756 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229323, d230756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229323, d230756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229325 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
    | true =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22843 q selected
  have h9 (q : Pattern) (selected : d229326 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229327 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229328 q = 0) : d230761 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229329 q = 0) : d230762 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229329, d230762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229329, d230762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229330 q = 0) : d230763 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229330, d230763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229330, d230763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22845 (p : Pattern) (selected : d229335 p = 0) : d230768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229320 q = 0) : d230753 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22841 q selected
    | true =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
  have h2 (q : Pattern) (selected : d229321 q = 0) : d230754 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229322 q = 0) : d230755 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229325 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
    | true =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22843 q selected
  have h5 (q : Pattern) (selected : d229326 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229327 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229328 q = 0) : d230761 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229333 q = 0) : d230766 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229333, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229333, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229334 q = 0) : d230767 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229334, d230767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229334, d230767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229335 q = 0) : d230768 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229335, d230768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229335, d230768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22846 (p : Pattern) (selected : d229341 p = 0) : d230774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229331 q = 0) : d230764 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229331, d230764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22844 q selected
    | true =>
      simp only [d229331, d230764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229332 q = 0) : d230765 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229332, d230765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229332, d230765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229336 q = 0) : d230769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229336, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22845 q selected
    | true =>
      simp only [d229336, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229337 q = 0) : d230770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229337, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229337, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229338 q = 0) : d230771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229338, d230771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229338, d230771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229339 q = 0) : d230772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229339, d230772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229339, d230772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229340 q = 0) : d230773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229340, d230773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229340, d230773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229341 q = 0) : d230774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229341, d230774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229341, d230774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22847 (p : Pattern) (selected : d229343 p = 0) : d230776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229325 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
    | true =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22843 q selected
  have h2 (q : Pattern) (selected : d229326 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229327 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229333 q = 0) : d230766 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229333, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229333, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229342 q = 0) : d230775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229342, d230775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229342, d230775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229343 q = 0) : d230776 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229343, d230776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229343, d230776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22848 (p : Pattern) (selected : d229349 p = 0) : d230782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229336 q = 0) : d230769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229336, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22845 q selected
    | true =>
      simp only [d229336, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229337 q = 0) : d230770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229337, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229337, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229344 q = 0) : d230777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229344, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22847 q selected
    | true =>
      simp only [d229344, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229345 q = 0) : d230778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229345, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229345, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229346 q = 0) : d230779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229346, d230779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229346, d230779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229347 q = 0) : d230780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229347, d230780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229347, d230780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229348 q = 0) : d230781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229348, d230781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229348, d230781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229349 q = 0) : d230782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229349, d230782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229349, d230782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22849 (p : Pattern) (selected : d229365 p = 0) : d230747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229351 q = 0) : d230731 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229351, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229351, d230731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22813 q selected
  have h2 (q : Pattern) (selected : d229180 q = 0) : d230566 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229180, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22813 q selected
    | true =>
      simp only [d229180, d230566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229352 q = 0) : d230732 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229352, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229352, d230732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229181 q = 0) : d230567 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229181, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229181, d230567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229353 q = 0) : d230733 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229353, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229353, d230733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229354 q = 0) : d230734 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229354, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229354, d230734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229355 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229355, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229355, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
  have h8 (q : Pattern) (selected : d229186 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
    | true =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229356 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229356, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229356, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229187 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229357 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229357, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229357, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229358 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229358, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229358, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229359 q = 0) : d230740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229359, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229359, d230740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229360 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
  have h15 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d229361 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d229362 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d229363 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d229364 q = 0) : d230746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229364, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229364, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d229365 q = 0) : d230747 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229365, d230747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229365, d230747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22850 (p : Pattern) (selected : d229367 p = 0) : d230752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229355 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229355, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229355, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
  have h2 (q : Pattern) (selected : d229186 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22814 q selected
    | true =>
      simp only [d229186, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229356 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229356, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229356, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229187 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229187, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229357 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229357, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229357, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229358 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229358, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229358, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229360 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
  have h8 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229361 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229362 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229363 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229364 q = 0) : d230746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229364, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229364, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229366 q = 0) : d230751 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229366, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229366, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229367 q = 0) : d230752 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229367, d230752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229367, d230752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22851 (p : Pattern) (selected : d229371 p = 0) : d230757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229360 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
  have h2 (q : Pattern) (selected : d229193 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22815 q selected
    | true =>
      simp only [d229193, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229361 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229361, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229194 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229194, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229362 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229362, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229363 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229363, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229366 q = 0) : d230751 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229366, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229366, d230751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229371 q = 0) : d230757 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229371, d230757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229371, d230757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22852 (p : Pattern) (selected : d229378 p = 0) : d230768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229368 q = 0) : d230753 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229368, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22849 q selected
    | true =>
      simp only [d229368, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22850 q selected
  have h2 (q : Pattern) (selected : d229369 q = 0) : d230754 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229369, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229369, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229370 q = 0) : d230755 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229370, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229370, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229372 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229372, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22850 q selected
    | true =>
      simp only [d229372, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22851 q selected
  have h5 (q : Pattern) (selected : d229373 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229373, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229373, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229374 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229374, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229374, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229375 q = 0) : d230761 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229375, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229375, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229376 q = 0) : d230766 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229376, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229376, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229377 q = 0) : d230767 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229377, d230767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229377, d230767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229378 q = 0) : d230768 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229378, d230768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229378, d230768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22853 (p : Pattern) (selected : d229382 p = 0) : d230776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229372 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229372, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22850 q selected
    | true =>
      simp only [d229372, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22851 q selected
  have h2 (q : Pattern) (selected : d229373 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229373, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229373, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229374 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229374, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229374, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229376 q = 0) : d230766 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229376, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229376, d230766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229381 q = 0) : d230775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229381, d230775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229381, d230775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229382 q = 0) : d230776 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229382, d230776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229382, d230776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22854 (p : Pattern) (selected : d229388 p = 0) : d230782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229379 q = 0) : d230769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229379, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22852 q selected
    | true =>
      simp only [d229379, d230769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229380 q = 0) : d230770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229380, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229380, d230770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229383 q = 0) : d230777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229383, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22853 q selected
    | true =>
      simp only [d229383, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229384 q = 0) : d230778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229384, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229384, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229385 q = 0) : d230779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229385, d230779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229385, d230779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229386 q = 0) : d230780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229386, d230780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229386, d230780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229387 q = 0) : d230781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229387, d230781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229387, d230781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229388 q = 0) : d230782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229388, d230782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229388, d230782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22855 (p : Pattern) (selected : d229392 p = 0) : d230787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229383 q = 0) : d230777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229383, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22853 q selected
    | true =>
      simp only [d229383, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229384 q = 0) : d230778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229384, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229384, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229389 q = 0) : d230784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229389, d230784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229389, d230784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229390 q = 0) : d230785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229390, d230785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229390, d230785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229391 q = 0) : d230786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229391, d230786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229391, d230786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229392 q = 0) : d230787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229392, d230787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229392, d230787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22856 (p : Pattern) (selected : d229395 p = 0) : d230790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229303 q = 0) : d230736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229303, d230736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
  have h2 (q : Pattern) (selected : d229087 q = 0) : d230572 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22793 q selected
    | true =>
      simp only [d229087, d230572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229304 q = 0) : d230737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229304, d230737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229088 q = 0) : d230573 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229088, d230573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229305 q = 0) : d230738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229305, d230738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229306 q = 0) : d230739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229306, d230739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229309 q = 0) : d230742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229309, d230742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
  have h8 (q : Pattern) (selected : d229094 q = 0) : d230579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22794 q selected
    | true =>
      simp only [d229094, d230579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229310 q = 0) : d230743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229310, d230743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229095 q = 0) : d230580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229095, d230580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229311 q = 0) : d230744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229311, d230744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229312 q = 0) : d230745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229312, d230745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229313 q = 0) : d230746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229313, d230746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229395 q = 0) : d230790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229395, d230790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229395, d230790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro22857 (p : Pattern) (selected : d229401 p = 0) : d230796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229320 q = 0) : d230753 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22841 q selected
    | true =>
      simp only [d229320, d230753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
  have h2 (q : Pattern) (selected : d229321 q = 0) : d230754 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229321, d230754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229322 q = 0) : d230755 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229322, d230755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229325 q = 0) : d230758 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22842 q selected
    | true =>
      simp only [d229325, d230758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22843 q selected
  have h5 (q : Pattern) (selected : d229326 q = 0) : d230759 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229326, d230759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229327 q = 0) : d230760 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229327, d230760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229328 q = 0) : d230761 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229328, d230761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229396 q = 0) : d230791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229396, d230791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22856 q selected
    | true =>
      simp only [d229396, d230791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229397 q = 0) : d230792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229397, d230792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229397, d230792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229398 q = 0) : d230793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229398, d230793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229398, d230793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229399 q = 0) : d230794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229399, d230794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229399, d230794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229400 q = 0) : d230795 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229400, d230795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229400, d230795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229401 q = 0) : d230796 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229401, d230796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229401, d230796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22858 (p : Pattern) (selected : d229407 p = 0) : d230802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229402 q = 0) : d230797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229402, d230797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22857 q selected
    | true =>
      simp only [d229402, d230797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229403 q = 0) : d230798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229403, d230798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229403, d230798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229404 q = 0) : d230799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229404, d230799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229404, d230799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229405 q = 0) : d230800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229405, d230800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229405, d230800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229406 q = 0) : d230801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229406, d230801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229406, d230801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229407 q = 0) : d230802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229407, d230802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229407, d230802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22859 (p : Pattern) (selected : d229413 p = 0) : d230808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229350 q = 0) : d230783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229350, d230783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22846 q selected
    | true =>
      simp only [d229350, d230783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22848 q selected
  have h2 (q : Pattern) (selected : d229393 q = 0) : d230788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229393, d230788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22854 q selected
    | true =>
      simp only [d229393, d230788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22855 q selected
  have h3 (q : Pattern) (selected : d229394 q = 0) : d230789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229394, d230789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229394, d230789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229408 q = 0) : d230803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229408, d230803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22858 q selected
    | true =>
      simp only [d229408, d230803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229409 q = 0) : d230804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229409, d230804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229409, d230804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229410 q = 0) : d230805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229410, d230805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229410, d230805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229411 q = 0) : d230806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229411, d230806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229411, d230806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229412 q = 0) : d230807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229412, d230807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229412, d230807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229413 q = 0) : d230808 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229413, d230808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229413, d230808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22860 (p : Pattern) (selected : d229418 p = 0) : d230787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229344 q = 0) : d230777 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229344, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22847 q selected
    | true =>
      simp only [d229344, d230777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229345 q = 0) : d230778 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229345, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229345, d230778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229415 q = 0) : d230784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229415, d230784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229415, d230784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229416 q = 0) : d230785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229416, d230785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229416, d230785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229417 q = 0) : d230786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229417, d230786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229417, d230786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229418 q = 0) : d230787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229418, d230787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229418, d230787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22861 (p : Pattern) (selected : d229424 p = 0) : d230815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229419 q = 0) : d230810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229419, d230810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22860 q selected
    | true =>
      simp only [d229419, d230810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229420 q = 0) : d230811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229420, d230811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229420, d230811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229421 q = 0) : d230812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229421, d230812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229421, d230812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229422 q = 0) : d230813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229422, d230813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229422, d230813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229423 q = 0) : d230814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229423, d230814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229423, d230814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229424 q = 0) : d230815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229424, d230815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229424, d230815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22862 (p : Pattern) (selected : d229430 p = 0) : d230821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229133 q = 0) : d230618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229133, d230618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229133, d230618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22802 q selected
  have h2 (q : Pattern) (selected : d229134 q = 0) : d230619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229134, d230619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229134, d230619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229143 q = 0) : d230628 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229143, d230628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22802 q selected
    | true =>
      simp only [d229143, d230628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22805 q selected
  have h4 (q : Pattern) (selected : d229144 q = 0) : d230629 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229144, d230629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229144, d230629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229145 q = 0) : d230630 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229145, d230630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229145, d230630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229271 q = 0) : d230704 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229271, d230704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22826 q selected
    | true =>
      simp only [d229271, d230704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22835 q selected
  have h7 (q : Pattern) (selected : d229284 q = 0) : d230717 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229284, d230717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22836 q selected
    | true =>
      simp only [d229284, d230717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22837 q selected
  have h8 (q : Pattern) (selected : d229285 q = 0) : d230718 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229285, d230718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229285, d230718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229286 q = 0) : d230719 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229286, d230719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229286, d230719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d229287 q = 0) : d230720 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229287, d230720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229287, d230720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229291 q = 0) : d230724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229291, d230724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229291, d230724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22838 q selected
  have h12 (q : Pattern) (selected : d229293 q = 0) : d230726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229293, d230726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229293, d230726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22839 q selected
  have h13 (q : Pattern) (selected : d229294 q = 0) : d230727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229294, d230727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229294, d230727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229295 q = 0) : d230728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229295, d230728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229295, d230728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229296 q = 0) : d230729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229296, d230729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d229296, d230729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d229297 q = 0) : d230730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229297, d230730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229297, d230730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229414 q = 0) : d230809 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229414, d230809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229414, d230809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22859 q selected
  have h18 (q : Pattern) (selected : d229425 q = 0) : d230816 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229425, d230816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229425, d230816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22861 q selected
  have h19 (q : Pattern) (selected : d229426 q = 0) : d230817 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229426, d230817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d229426, d230817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d229427 q = 0) : d230818 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229427, d230818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d229427, d230818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d229428 q = 0) : d230819 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229428, d230819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d229428, d230819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d229429 q = 0) : d230820 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229429, d230820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d229429, d230820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d229430 q = 0) : d230821 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d229430, d230821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229430, d230821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22863 (p : Pattern) (selected : d229436 p = 0) : d230827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229431 q = 0) : d230822 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d229431, d230822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229431, d230822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22862 q selected
  have h2 (q : Pattern) (selected : d229432 q = 0) : d230823 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d229432, d230823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229432, d230823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229433 q = 0) : d230824 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d229433, d230824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229433, d230824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229434 q = 0) : d230825 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d229434, d230825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229434, d230825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229435 q = 0) : d230826 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d229435, d230826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229435, d230826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229436 q = 0) : d230827 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d229436, d230827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229436, d230827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22864 (p : Pattern) (selected : d229442 p = 0) : d230833 p = 1 := by
  have h0 (q : Pattern) (selected : d228111 q = 0) : d229823 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228111, d229823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22560 q selected
    | true =>
      simp only [d228111, d229823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22594 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d228390 q = 0) : d230042 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228390, d230042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228390, d230042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22652 q selected
  have h3 (q : Pattern) (selected : d228391 q = 0) : d230043 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d228391, d230043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228391, d230043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228702 q = 0) : d230282 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228702, d230282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228702, d230282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22718 q selected
  have h5 (q : Pattern) (selected : d228703 q = 0) : d230283 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d228703, d230283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228703, d230283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228704 q = 0) : d230284 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d228704, d230284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228704, d230284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229075 q = 0) : d230560 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d229075, d230560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229075, d230560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22791 q selected
  have h8 (q : Pattern) (selected : d229076 q = 0) : d230561 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d229076, d230561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229076, d230561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229077 q = 0) : d230562 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d229077, d230562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229077, d230562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229078 q = 0) : d230563 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d229078, d230563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229078, d230563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229437 q = 0) : d230828 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d229437, d230828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229437, d230828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22863 q selected
  have h12 (q : Pattern) (selected : d229438 q = 0) : d230829 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d229438, d230829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229438, d230829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229439 q = 0) : d230830 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d229439, d230830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229439, d230830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229440 q = 0) : d230831 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d229440, d230831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229440, d230831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229441 q = 0) : d230832 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d229441, d230832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229441, d230832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229442 q = 0) : d230833 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d229442, d230833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229442, d230833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22865 (p : Pattern) (selected : d229448 p = 0) : d230839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229443 q = 0) : d230834 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d229443, d230834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22864 q selected
    | true =>
      simp only [d229443, d230834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229444 q = 0) : d230835 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d229444, d230835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229444, d230835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229445 q = 0) : d230836 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d229445, d230836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229445, d230836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229446 q = 0) : d230837 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d229446, d230837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229446, d230837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229447 q = 0) : d230838 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d229447, d230838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229447, d230838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229448 q = 0) : d230839 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d229448, d230839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229448, d230839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22866 (p : Pattern) (selected : d229454 p = 0) : d230845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229449 q = 0) : d230840 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d229449, d230840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22865 q selected
    | true =>
      simp only [d229449, d230840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229450 q = 0) : d230841 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d229450, d230841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229450, d230841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229451 q = 0) : d230842 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d229451, d230842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229451, d230842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229452 q = 0) : d230843 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d229452, d230843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229452, d230843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229453 q = 0) : d230844 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d229453, d230844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229453, d230844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229454 q = 0) : d230845 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d229454, d230845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229454, d230845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22867 (p : Pattern) (selected : d229459 p = 0) : d230850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229455 q = 0) : d230846 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d229455, d230846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22866 q selected
    | true =>
      simp only [d229455, d230846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229456 q = 0) : d230847 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d229456, d230847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229456, d230847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229457 q = 0) : d230848 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d229457, d230848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229457, d230848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229458 q = 0) : d230849 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d229458, d230849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229458, d230849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229459 q = 0) : d230850 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d229459, d230850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229459, d230850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22868 (p : Pattern) (selected : d229465 p = 0) : d230856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229460 q = 0) : d230851 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d229460, d230851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22867 q selected
    | true =>
      simp only [d229460, d230851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229461 q = 0) : d230852 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d229461, d230852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229461, d230852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229462 q = 0) : d230853 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d229462, d230853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229462, d230853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229463 q = 0) : d230854 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d229463, d230854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229463, d230854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229464 q = 0) : d230855 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d229464, d230855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229464, d230855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229465 q = 0) : d230856 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d229465, d230856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229465, d230856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22869 (p : Pattern) (selected : d229471 p = 0) : d230862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229466 q = 0) : d230857 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d229466, d230857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22868 q selected
    | true =>
      simp only [d229466, d230857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229467 q = 0) : d230858 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d229467, d230858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229467, d230858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229468 q = 0) : d230859 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d229468, d230859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229468, d230859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229469 q = 0) : d230860 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d229469, d230860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229469, d230860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229470 q = 0) : d230861 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d229470, d230861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229470, d230861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229471 q = 0) : d230862 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d229471, d230862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229471, d230862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22870 (p : Pattern) (selected : d229477 p = 0) : d230868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229472 q = 0) : d230863 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d229472, d230863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22869 q selected
    | true =>
      simp only [d229472, d230863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229473 q = 0) : d230864 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d229473, d230864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229473, d230864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229474 q = 0) : d230865 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d229474, d230865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229474, d230865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229475 q = 0) : d230866 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d229475, d230866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229475, d230866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229476 q = 0) : d230867 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d229476, d230867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229476, d230867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229477 q = 0) : d230868 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d229477, d230868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229477, d230868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22871 (p : Pattern) (selected : d229483 p = 0) : d230874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d229478 q = 0) : d230869 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d229478, d230869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22870 q selected
    | true =>
      simp only [d229478, d230869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229479 q = 0) : d230870 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d229479, d230870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229479, d230870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229480 q = 0) : d230871 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d229480, d230871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229480, d230871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229481 q = 0) : d230872 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d229481, d230872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229481, d230872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229482 q = 0) : d230873 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d229482, d230873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229482, d230873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229483 q = 0) : d230874 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d229483, d230874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229483, d230874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22872 (p : Pattern) (selected : d227815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227814 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227815 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22873 (p : Pattern) (selected : d227821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227818 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227819 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227820 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227821 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22874 (p : Pattern) (selected : d227827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22873 q selected
    | true =>
      simp only [d227822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227826 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227827 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22875 (p : Pattern) (selected : d227833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22874 q selected
    | true =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227830 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227831 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227832 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22876 (p : Pattern) (selected : d227839 p = 1) : d230879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227786 q = 1) : d227786 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227792 q = 1) : d227792 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d227813 q = 1) : d227813 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d227834 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22875 q selected
    | true =>
      simp only [d227834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227835 q = 1) : d230875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227835, d230875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227835, d230875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227709 q = 1) : d227709 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d227836 q = 1) : d230876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227836, d230876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227836, d230876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227837 q = 1) : d230877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227837, d230877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227837, d230877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227838 q = 1) : d230878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227838, d230878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227838, d230878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227839 q = 1) : d230879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227839, d230879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227839, d230879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22877 (p : Pattern) (selected : d227851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22874 q selected
    | true =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227830 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227831 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227832 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227851 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22878 (p : Pattern) (selected : d227857 p = 1) : d230884 p = 1 := by
  have h0 (q : Pattern) (selected : d227786 q = 1) : d227786 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227792 q = 1) : d227792 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227813 q = 1) : d227813 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d227834 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22875 q selected
    | true =>
      simp only [d227834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227835 q = 1) : d230875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227835, d230875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227835, d230875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227709 q = 1) : d227709 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d227836 q = 1) : d230876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227836, d230876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227836, d230876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227837 q = 1) : d230877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227837, d230877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227837, d230877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227838 q = 1) : d230878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227838, d230878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227838, d230878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227844 q = 1) : d227844 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d227848 q = 1) : d227848 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d227850 q = 1) : d227850 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d227852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22877 q selected
    | true =>
      simp only [d227852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d227853 q = 1) : d230880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227853, d230880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227853, d230880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d227716 q = 1) : d227716 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d227854 q = 1) : d230881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227854, d230881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227854, d230881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227855 q = 1) : d230882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227855, d230882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227855, d230882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d227856 q = 1) : d230883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227856, d230883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227856, d230883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d227857 q = 1) : d230884 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227857, d230884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227857, d230884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22879 (p : Pattern) (selected : d227866 p = 1) : d230891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227850 q = 1) : d227850 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22877 q selected
    | true =>
      simp only [d227852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227853 q = 1) : d230880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227853, d230880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227853, d230880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227716 q = 1) : d227716 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d227854 q = 1) : d230881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227854, d230881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227854, d230881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227864 q = 1) : d230889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227864, d230889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227864, d230889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227865 q = 1) : d230890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227865, d230890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227865, d230890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227866 q = 1) : d230891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227866, d230891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227866, d230891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22880 (p : Pattern) (selected : d227896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
  have h2 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227895 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227896 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22881 (p : Pattern) (selected : d227902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227897 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22880 q selected
    | true =>
      simp only [d227897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227898 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227899 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227900 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227901 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227902 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22882 (p : Pattern) (selected : d227908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22881 q selected
    | true =>
      simp only [d227903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227905 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227906 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227907 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22883 (p : Pattern) (selected : d227914 p = 1) : d230901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227890 q = 1) : d227890 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22882 q selected
    | true =>
      simp only [d227909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227910 q = 1) : d230897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227910, d230897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227910, d230897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227750 q = 1) : d227750 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d227911 q = 1) : d230898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227911, d230898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227911, d230898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227912 q = 1) : d230899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227912, d230899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227912, d230899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227913 q = 1) : d230900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227913, d230900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227913, d230900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227914 q = 1) : d230901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227914, d230901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227914, d230901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22884 (p : Pattern) (selected : d227920 p = 1) : d230907 p = 1 := by
  have h0 (q : Pattern) (selected : d227780 q = 1) : d227780 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227858 q = 1) : d230885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227858, d230885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22876 q selected
    | true =>
      simp only [d227858, d230885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22878 q selected
  have h2 (q : Pattern) (selected : d227860 q = 1) : d227860 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d227861 q = 1) : d230886 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227861, d230886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227861, d230886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d227862 q = 1) : d230887 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227862, d230887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227862, d230887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227863 q = 1) : d230888 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227863, d230888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227863, d230888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227867 q = 1) : d230892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227867, d230892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227867, d230892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22879 q selected
  have h8 (q : Pattern) (selected : d227868 q = 1) : d230893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227868, d230893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227868, d230893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d227869 q = 1) : d230894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227869, d230894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227869, d230894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d227870 q = 1) : d230895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227870, d230895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227870, d230895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d227871 q = 1) : d230896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227871, d230896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227871, d230896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227915 q = 1) : d230902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227915, d230902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227915, d230902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22883 q selected
  have h13 (q : Pattern) (selected : d227916 q = 1) : d230903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227916, d230903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227916, d230903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d227917 q = 1) : d230904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227917, d230904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d227917, d230904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d227918 q = 1) : d230905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227918, d230905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227918, d230905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d227919 q = 1) : d230906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227919, d230906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227919, d230906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d227920 q = 1) : d230907 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d227920, d230907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227920, d230907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro22885 (p : Pattern) (selected : d227926 p = 1) : d230913 p = 1 := by
  have h0 (q : Pattern) (selected : d227765 q = 1) : d227765 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227921 q = 1) : d230908 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d227921, d230908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227921, d230908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22884 q selected
  have h3 (q : Pattern) (selected : d227922 q = 1) : d230909 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d227922, d230909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227922, d230909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227923 q = 1) : d230910 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d227923, d230910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227923, d230910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227924 q = 1) : d230911 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d227924, d230911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227924, d230911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227925 q = 1) : d230912 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d227925, d230912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227925, d230912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227926 q = 1) : d230913 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d227926, d230913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227926, d230913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22886 (p : Pattern) (selected : d227976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227975 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227814 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227976 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22887 (p : Pattern) (selected : d227982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227818 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227819 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227981 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227820 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227982 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22888 (p : Pattern) (selected : d227988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227983 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22887 q selected
    | true =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22873 q selected
  have h2 (q : Pattern) (selected : d227984 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227985 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227822 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22873 q selected
    | true =>
      simp only [d227822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227986 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227987 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227988 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22889 (p : Pattern) (selected : d227994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227989 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22888 q selected
    | true =>
      simp only [d227989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227990 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22874 q selected
    | true =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227991 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227992 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227993 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227994 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22890 (p : Pattern) (selected : d228006 p = 1) : d230918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227947 q = 1) : d227947 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227953 q = 1) : d227953 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d227974 q = 1) : d227974 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d227995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22889 q selected
    | true =>
      simp only [d227995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22875 q selected
  have h5 (q : Pattern) (selected : d227996 q = 1) : d230914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227996, d230914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227996, d230914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228002 q = 1) : d228002 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d228003 q = 1) : d230915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228003, d230915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228003, d230915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228004 q = 1) : d230916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228004, d230916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228004, d230916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228005 q = 1) : d230917 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228005, d230917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228005, d230917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228006 q = 1) : d230918 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228006, d230918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228006, d230918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22891 (p : Pattern) (selected : d228018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227989 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22888 q selected
    | true =>
      simp only [d227989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227990 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22874 q selected
    | true =>
      simp only [d227828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227991 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227992 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227993 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228018 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22892 (p : Pattern) (selected : d228027 p = 1) : d230923 p = 1 := by
  have h0 (q : Pattern) (selected : d227947 q = 1) : d227947 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227953 q = 1) : d227953 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d227974 q = 1) : d227974 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d227995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22889 q selected
    | true =>
      simp only [d227995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22875 q selected
  have h4 (q : Pattern) (selected : d227996 q = 1) : d230914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227996, d230914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227996, d230914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228002 q = 1) : d228002 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d228003 q = 1) : d230915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228003, d230915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228003, d230915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228004 q = 1) : d230916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228004, d230916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228004, d230916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228005 q = 1) : d230917 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228005, d230917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228005, d230917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228011 q = 1) : d228011 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d228015 q = 1) : d228015 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d228017 q = 1) : d228017 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d228019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22891 q selected
    | true =>
      simp only [d228019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22877 q selected
  have h13 (q : Pattern) (selected : d228020 q = 1) : d230919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228020, d230919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228020, d230919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228023 q = 1) : d228023 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228024 q = 1) : d230920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228024, d230920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228024, d230920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228025 q = 1) : d230921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228025, d230921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228025, d230921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228026 q = 1) : d230922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228026, d230922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228026, d230922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228027 q = 1) : d230923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228027, d230923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228027, d230923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22893 (p : Pattern) (selected : d228036 p = 1) : d230930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228017 q = 1) : d228017 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228019 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22891 q selected
    | true =>
      simp only [d228019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22877 q selected
  have h3 (q : Pattern) (selected : d228020 q = 1) : d230919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228020, d230919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228020, d230919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228023 q = 1) : d228023 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228024 q = 1) : d230920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228024, d230920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228024, d230920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228034 q = 1) : d230928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228034, d230928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228034, d230928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228035 q = 1) : d230929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228035, d230929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228035, d230929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228036 q = 1) : d230930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228036, d230930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228036, d230930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22894 (p : Pattern) (selected : d228068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
  have h2 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
  have h8 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227895 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228068 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22895 (p : Pattern) (selected : d228074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22894 q selected
    | true =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22880 q selected
  have h2 (q : Pattern) (selected : d228070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227897 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22880 q selected
    | true =>
      simp only [d227897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227898 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227899 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227900 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228073 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228074 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22896 (p : Pattern) (selected : d228080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228075 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22895 q selected
    | true =>
      simp only [d228075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228076 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22881 q selected
    | true =>
      simp only [d227903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22897 (p : Pattern) (selected : d228092 p = 1) : d230940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228062 q = 1) : d228062 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22896 q selected
    | true =>
      simp only [d228081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22882 q selected
  have h3 (q : Pattern) (selected : d228082 q = 1) : d230936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228082, d230936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228082, d230936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228088 q = 1) : d228088 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228089 q = 1) : d230937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228089, d230937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228089, d230937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228090 q = 1) : d230938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228090, d230938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228090, d230938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228091 q = 1) : d230939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228091, d230939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228091, d230939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228092 q = 1) : d230940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228092, d230940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228092, d230940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22898 (p : Pattern) (selected : d228104 p = 1) : d230946 p = 1 := by
  have h0 (q : Pattern) (selected : d227941 q = 1) : d227941 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228028 q = 1) : d230924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228028, d230924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22890 q selected
    | true =>
      simp only [d228028, d230924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22892 q selected
  have h2 (q : Pattern) (selected : d228030 q = 1) : d228030 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228031 q = 1) : d230925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228031, d230925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228031, d230925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228032 q = 1) : d230926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228032, d230926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228032, d230926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228033 q = 1) : d230927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228033, d230927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228033, d230927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228037 q = 1) : d230931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228037, d230931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228037, d230931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22893 q selected
  have h8 (q : Pattern) (selected : d228039 q = 1) : d228039 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d228040 q = 1) : d230932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228040, d230932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228040, d230932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228041 q = 1) : d230933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228041, d230933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228041, d230933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d228042 q = 1) : d230934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228042, d230934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228042, d230934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d228043 q = 1) : d230935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228043, d230935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228043, d230935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228093 q = 1) : d230941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228093, d230941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228093, d230941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22897 q selected
  have h14 (q : Pattern) (selected : d228099 q = 1) : d228099 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228100 q = 1) : d230942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228100, d230942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228100, d230942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228101 q = 1) : d230943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228101, d230943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228101, d230943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d228102 q = 1) : d230944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228102, d230944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228102, d230944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d228103 q = 1) : d230945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228103, d230945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228103, d230945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d228104 q = 1) : d230946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228104, d230946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228104, d230946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22899 (p : Pattern) (selected : d228110 p = 1) : d230952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228105 q = 1) : d230947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228105, d230947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228105, d230947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22898 q selected
  have h2 (q : Pattern) (selected : d228106 q = 1) : d230948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228106, d230948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228106, d230948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228107 q = 1) : d230949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228107, d230949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228107, d230949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228108 q = 1) : d230950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228108, d230950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228108, d230950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228109 q = 1) : d230951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228109, d230951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228109, d230951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228110 q = 1) : d230952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228110, d230952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228110, d230952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22900 (p : Pattern) (selected : d228187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d862 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro50 q selected
    | true =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d863 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228186 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227975 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228187 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22901 (p : Pattern) (selected : d228193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227818 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227819 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227981 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228193 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22902 (p : Pattern) (selected : d228200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22901 q selected
    | true =>
      simp only [d228194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22887 q selected
  have h2 (q : Pattern) (selected : d228195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227983 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22887 q selected
    | true =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22873 q selected
  have h5 (q : Pattern) (selected : d227984 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227985 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228198 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228199 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228200 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22903 (p : Pattern) (selected : d228204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227983 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22887 q selected
    | true =>
      simp only [d227983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22873 q selected
  have h2 (q : Pattern) (selected : d227984 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227985 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228198 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228203 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228204 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22904 (p : Pattern) (selected : d228210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22902 q selected
    | true =>
      simp only [d228201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22903 q selected
    | true =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22905 (p : Pattern) (selected : d228214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22903 q selected
    | true =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22906 (p : Pattern) (selected : d228235 p = 1) : d230958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228155 q = 1) : d228155 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228164 q = 1) : d228164 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228185 q = 1) : d228185 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d228215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22904 q selected
    | true =>
      simp only [d228215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22905 q selected
  have h5 (q : Pattern) (selected : d228216 q = 1) : d230954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228216, d230954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228216, d230954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228231 q = 1) : d228231 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d228232 q = 1) : d230955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228232, d230955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228232, d230955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228233 q = 1) : d230956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228233, d230956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228233, d230956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228234 q = 1) : d230957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228234, d230957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228234, d230957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228235 q = 1) : d230958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228235, d230958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228235, d230958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22907 (p : Pattern) (selected : d228249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22902 q selected
    | true =>
      simp only [d228201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22903 q selected
    | true =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228249 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22908 (p : Pattern) (selected : d228250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22903 q selected
    | true =>
      simp only [d228205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228250 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22909 (p : Pattern) (selected : d228259 p = 1) : d230963 p = 1 := by
  have h0 (q : Pattern) (selected : d228155 q = 1) : d228155 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228164 q = 1) : d228164 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228185 q = 1) : d228185 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22904 q selected
    | true =>
      simp only [d228215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22905 q selected
  have h4 (q : Pattern) (selected : d228216 q = 1) : d230954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228216, d230954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228216, d230954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228231 q = 1) : d228231 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d228232 q = 1) : d230955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228232, d230955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228232, d230955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228233 q = 1) : d230956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228233, d230956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228233, d230956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228234 q = 1) : d230957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228234, d230957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228234, d230957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228241 q = 1) : d228241 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d228246 q = 1) : d228246 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d228248 q = 1) : d228248 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d228251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22907 q selected
    | true =>
      simp only [d228251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22908 q selected
  have h13 (q : Pattern) (selected : d228252 q = 1) : d230959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228252, d230959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228252, d230959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228255 q = 1) : d228255 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228256 q = 1) : d230960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228256, d230960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228256, d230960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228257 q = 1) : d230961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228257, d230961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228257, d230961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228258 q = 1) : d230962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228258, d230962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228258, d230962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228259 q = 1) : d230963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228259, d230963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228259, d230963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22910 (p : Pattern) (selected : d228279 p = 1) : d230970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228248 q = 1) : d228248 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22907 q selected
    | true =>
      simp only [d228251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22908 q selected
  have h3 (q : Pattern) (selected : d228252 q = 1) : d230959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228252, d230959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228252, d230959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228255 q = 1) : d228255 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228256 q = 1) : d230960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228256, d230960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228256, d230960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228277 q = 1) : d230968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228277, d230968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228277, d230968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228278 q = 1) : d230969 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228278, d230969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228278, d230969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228279 q = 1) : d230970 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228279, d230970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228279, d230970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22911 (p : Pattern) (selected : d228324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228319 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
  have h2 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228322 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
  have h8 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228323 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227891 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
  have h15 (q : Pattern) (selected : d227816 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22872 q selected
    | true =>
      simp only [d227816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d227892 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227817 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d227893 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d227893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d227894 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d227894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228324 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22912 (p : Pattern) (selected : d228331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22911 q selected
    | true =>
      simp only [d228325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22894 q selected
  have h2 (q : Pattern) (selected : d228326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22894 q selected
    | true =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22880 q selected
  have h5 (q : Pattern) (selected : d228070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228328 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228329 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228330 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228331 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22913 (p : Pattern) (selected : d228335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22894 q selected
    | true =>
      simp only [d228069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22880 q selected
  have h2 (q : Pattern) (selected : d228070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228329 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228334 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228335 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22914 (p : Pattern) (selected : d228341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228332 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22912 q selected
    | true =>
      simp only [d228332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228333 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22913 q selected
    | true =>
      simp only [d228336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22915 (p : Pattern) (selected : d228345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22913 q selected
    | true =>
      simp only [d228336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228342 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228343 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228344 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228345 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22916 (p : Pattern) (selected : d228366 p = 1) : d230980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228318 q = 1) : d228318 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228346 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22914 q selected
    | true =>
      simp only [d228346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22915 q selected
  have h3 (q : Pattern) (selected : d228347 q = 1) : d230976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228347, d230976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228347, d230976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228362 q = 1) : d228362 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228363 q = 1) : d230977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228363, d230977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228363, d230977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228364 q = 1) : d230978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228364, d230978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228364, d230978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228365 q = 1) : d230979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228365, d230979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228365, d230979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228366 q = 1) : d230980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228366, d230980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228366, d230980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22917 (p : Pattern) (selected : d228383 p = 1) : d230986 p = 1 := by
  have h0 (q : Pattern) (selected : d228147 q = 1) : d228147 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228260 q = 1) : d230964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228260, d230964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22906 q selected
    | true =>
      simp only [d228260, d230964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22909 q selected
  have h2 (q : Pattern) (selected : d228273 q = 1) : d228273 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228274 q = 1) : d230965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228274, d230965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228274, d230965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228275 q = 1) : d230966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228275, d230966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228275, d230966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228276 q = 1) : d230967 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228276, d230967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228276, d230967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228280 q = 1) : d230971 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228280, d230971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228280, d230971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22910 q selected
  have h8 (q : Pattern) (selected : d228282 q = 1) : d228282 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d228283 q = 1) : d230972 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228283, d230972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228283, d230972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228284 q = 1) : d230973 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228284, d230973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228284, d230973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d228285 q = 1) : d230974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228285, d230974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228285, d230974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d228286 q = 1) : d230975 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228286, d230975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228286, d230975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228367 q = 1) : d230981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228367, d230981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228367, d230981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22916 q selected
  have h14 (q : Pattern) (selected : d228378 q = 1) : d228378 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228379 q = 1) : d230982 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228379, d230982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228379, d230982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228380 q = 1) : d230983 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228380, d230983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228380, d230983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d228381 q = 1) : d230984 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228381, d230984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228381, d230984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d228382 q = 1) : d230985 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228382, d230985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228382, d230985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d228383 q = 1) : d230986 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228383, d230986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228383, d230986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22918 (p : Pattern) (selected : d228389 p = 1) : d230992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228384 q = 1) : d230987 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228384, d230987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228384, d230987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22917 q selected
  have h2 (q : Pattern) (selected : d228385 q = 1) : d230988 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228385, d230988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228385, d230988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228386 q = 1) : d230989 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228386, d230989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228386, d230989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228387 q = 1) : d230990 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228387, d230990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228387, d230990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228388 q = 1) : d230991 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228388, d230991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228388, d230991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228389 q = 1) : d230992 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228389, d230992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228389, d230992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22919 (p : Pattern) (selected : d228477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1243 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro77 q selected
    | true =>
      simp only [d1243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1244 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d862 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro50 q selected
    | true =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d863 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1245 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228476 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228186 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228477 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22920 (p : Pattern) (selected : d228483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22919 q selected
    | true =>
      simp only [d228478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228482 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228483 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22921 (p : Pattern) (selected : d228485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228485 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22922 (p : Pattern) (selected : d228489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227979 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227980 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228484 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228489 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22923 (p : Pattern) (selected : d228496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22920 q selected
    | true =>
      simp only [d228486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22921 q selected
  have h2 (q : Pattern) (selected : d228487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228490 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22921 q selected
    | true =>
      simp only [d228490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22922 q selected
  have h5 (q : Pattern) (selected : d228491 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228492 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228493 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228495 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228496 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22924 (p : Pattern) (selected : d228500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228490 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22921 q selected
    | true =>
      simp only [d228490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22922 q selected
  have h2 (q : Pattern) (selected : d228491 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228492 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228494 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228499 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228500 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22925 (p : Pattern) (selected : d228506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228497 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22923 q selected
    | true =>
      simp only [d228497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228498 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22924 q selected
    | true =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228506 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22926 (p : Pattern) (selected : d228510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22924 q selected
    | true =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228507 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228508 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228510 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22927 (p : Pattern) (selected : d228531 p = 1) : d230999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228445 q = 1) : d228445 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228454 q = 1) : d228454 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228475 q = 1) : d228475 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d228511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22925 q selected
    | true =>
      simp only [d228511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22926 q selected
  have h5 (q : Pattern) (selected : d228512 q = 1) : d230995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228512, d230995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228512, d230995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228527 q = 1) : d228527 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d228528 q = 1) : d230996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228528, d230996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228528, d230996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228529 q = 1) : d230997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228529, d230997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228529, d230997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228530 q = 1) : d230998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228530, d230998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228530, d230998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228531 q = 1) : d230999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228531, d230999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228531, d230999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22928 (p : Pattern) (selected : d228545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228497 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22923 q selected
    | true =>
      simp only [d228497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228498 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22924 q selected
    | true =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22929 (p : Pattern) (selected : d228546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22924 q selected
    | true =>
      simp only [d228501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228507 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228508 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228509 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22930 (p : Pattern) (selected : d228555 p = 1) : d231004 p = 1 := by
  have h0 (q : Pattern) (selected : d228445 q = 1) : d228445 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228454 q = 1) : d228454 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228475 q = 1) : d228475 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22925 q selected
    | true =>
      simp only [d228511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22926 q selected
  have h4 (q : Pattern) (selected : d228512 q = 1) : d230995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228512, d230995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228512, d230995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228527 q = 1) : d228527 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d228528 q = 1) : d230996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228528, d230996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228528, d230996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228529 q = 1) : d230997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228529, d230997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228529, d230997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228530 q = 1) : d230998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228530, d230998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228530, d230998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228537 q = 1) : d228537 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d228542 q = 1) : d228542 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d228544 q = 1) : d228544 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d228547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22928 q selected
    | true =>
      simp only [d228547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22929 q selected
  have h13 (q : Pattern) (selected : d228548 q = 1) : d231000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228548, d231000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228548, d231000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228551 q = 1) : d228551 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228552 q = 1) : d231001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228552, d231001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228552, d231001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228553 q = 1) : d231002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228553, d231002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228553, d231002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228554 q = 1) : d231003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228554, d231003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228554, d231003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228555 q = 1) : d231004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228555, d231004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228555, d231004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22931 (p : Pattern) (selected : d228575 p = 1) : d231011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228544 q = 1) : d228544 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22928 q selected
    | true =>
      simp only [d228547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22929 q selected
  have h3 (q : Pattern) (selected : d228548 q = 1) : d231000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228548, d231000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228548, d231000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228551 q = 1) : d228551 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228552 q = 1) : d231001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228552, d231001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228552, d231001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228573 q = 1) : d231009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228573, d231009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228573, d231009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228574 q = 1) : d231010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228574, d231010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228574, d231010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228575 q = 1) : d231011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228575, d231011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228575, d231011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22932 (p : Pattern) (selected : d228630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228625 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22919 q selected
  have h2 (q : Pattern) (selected : d228478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22919 q selected
    | true =>
      simp only [d228478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228626 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228627 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228628 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228319 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
  have h8 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228322 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228629 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
  have h15 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d228065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d228066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228323 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22933 (p : Pattern) (selected : d228632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228319 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
  have h2 (q : Pattern) (selected : d228188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22900 q selected
    | true =>
      simp only [d228188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228322 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
  have h8 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228323 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228631 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228632 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22934 (p : Pattern) (selected : d228636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
  have h2 (q : Pattern) (selected : d227977 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22886 q selected
    | true =>
      simp only [d227977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227978 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228631 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228636 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22935 (p : Pattern) (selected : d228643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228633 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22932 q selected
    | true =>
      simp only [d228633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22933 q selected
  have h2 (q : Pattern) (selected : d228634 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228635 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22933 q selected
    | true =>
      simp only [d228637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22934 q selected
  have h5 (q : Pattern) (selected : d228638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228640 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228641 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228642 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228643 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22936 (p : Pattern) (selected : d228647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228637 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22933 q selected
    | true =>
      simp only [d228637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22934 q selected
  have h2 (q : Pattern) (selected : d228638 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228639 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228641 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228646 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228647 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22937 (p : Pattern) (selected : d228653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228644 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22935 q selected
    | true =>
      simp only [d228644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228645 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22936 q selected
    | true =>
      simp only [d228648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22938 (p : Pattern) (selected : d228657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228648 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22936 q selected
    | true =>
      simp only [d228648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228649 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22939 (p : Pattern) (selected : d228678 p = 1) : d231021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228624 q = 1) : d228624 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22937 q selected
    | true =>
      simp only [d228658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22938 q selected
  have h3 (q : Pattern) (selected : d228659 q = 1) : d231017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228659, d231017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228659, d231017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228674 q = 1) : d228674 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228675 q = 1) : d231018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228675, d231018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228675, d231018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228676 q = 1) : d231019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228676, d231019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228676, d231019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228677 q = 1) : d231020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228677, d231020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228677, d231020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228678 q = 1) : d231021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228678, d231021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228678, d231021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22940 (p : Pattern) (selected : d228695 p = 1) : d231027 p = 1 := by
  have h0 (q : Pattern) (selected : d228437 q = 1) : d228437 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228556 q = 1) : d231005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228556, d231005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22927 q selected
    | true =>
      simp only [d228556, d231005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22930 q selected
  have h2 (q : Pattern) (selected : d228569 q = 1) : d228569 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228570 q = 1) : d231006 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228570, d231006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228570, d231006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228571 q = 1) : d231007 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228571, d231007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228571, d231007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228572 q = 1) : d231008 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228572, d231008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228572, d231008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228576 q = 1) : d231012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228576, d231012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228576, d231012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22931 q selected
  have h8 (q : Pattern) (selected : d228578 q = 1) : d228578 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d228579 q = 1) : d231013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228579, d231013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228579, d231013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228580 q = 1) : d231014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228580, d231014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228580, d231014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d228581 q = 1) : d231015 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228581, d231015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228581, d231015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d228582 q = 1) : d231016 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228582, d231016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228582, d231016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228679 q = 1) : d231022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228679, d231022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228679, d231022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22939 q selected
  have h14 (q : Pattern) (selected : d228690 q = 1) : d228690 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228691 q = 1) : d231023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228691, d231023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228691, d231023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228692 q = 1) : d231024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228692, d231024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228692, d231024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d228693 q = 1) : d231025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228693, d231025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228693, d231025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d228694 q = 1) : d231026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228694, d231026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228694, d231026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d228695 q = 1) : d231027 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228695, d231027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228695, d231027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22941 (p : Pattern) (selected : d228701 p = 1) : d231033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228696 q = 1) : d231028 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228696, d231028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228696, d231028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22940 q selected
  have h2 (q : Pattern) (selected : d228697 q = 1) : d231029 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228697, d231029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228697, d231029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228698 q = 1) : d231030 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228698, d231030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228698, d231030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228699 q = 1) : d231031 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228699, d231031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228699, d231031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228700 q = 1) : d231032 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228700, d231032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228700, d231032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228701 q = 1) : d231033 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228701, d231033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228701, d231033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22942 (p : Pattern) (selected : d228813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1700 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro108 q selected
    | true =>
      simp only [d1700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1701 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1705 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro109 q selected
    | true =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1706 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1707 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228811 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1722 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228812 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228813 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22943 (p : Pattern) (selected : d228819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1705 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro109 q selected
    | true =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1706 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1722 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228812 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1737 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228818 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228819 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22944 (p : Pattern) (selected : d228826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1737 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228818 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1749 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228825 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228826 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22945 (p : Pattern) (selected : d228832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228814 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22942 q selected
    | true =>
      simp only [d228814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228815 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228816 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228817 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228820 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
    | true =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228821 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228822 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228823 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228824 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228829 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228830 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228831 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228832 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22946 (p : Pattern) (selected : d228834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228820 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
    | true =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228821 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228822 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228823 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228829 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228830 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228831 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228833 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228834 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22947 (p : Pattern) (selected : d228838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228829 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228830 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228833 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228838 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22948 (p : Pattern) (selected : d228845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228835 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22945 q selected
    | true =>
      simp only [d228835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22946 q selected
  have h2 (q : Pattern) (selected : d228836 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228837 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228839 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22946 q selected
    | true =>
      simp only [d228839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22947 q selected
  have h5 (q : Pattern) (selected : d228840 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228841 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228842 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228843 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228844 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228845 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22949 (p : Pattern) (selected : d228849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228839 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22946 q selected
    | true =>
      simp only [d228839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22947 q selected
  have h2 (q : Pattern) (selected : d228840 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228841 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228843 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228848 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228849 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22950 (p : Pattern) (selected : d228855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22948 q selected
    | true =>
      simp only [d228846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22949 q selected
    | true =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228852 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22951 (p : Pattern) (selected : d228859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22949 q selected
    | true =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228859 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22952 (p : Pattern) (selected : d228880 p = 1) : d231041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228780 q = 1) : d228780 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228789 q = 1) : d228789 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228810 q = 1) : d228810 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d228860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22950 q selected
    | true =>
      simp only [d228860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22951 q selected
  have h5 (q : Pattern) (selected : d228861 q = 1) : d231037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228861, d231037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228861, d231037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228876 q = 1) : d228876 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d228877 q = 1) : d231038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228877, d231038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228877, d231038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228878 q = 1) : d231039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228878, d231039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228878, d231039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228879 q = 1) : d231040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228879, d231040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228879, d231040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228880 q = 1) : d231041 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228880, d231041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228880, d231041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22953 (p : Pattern) (selected : d228894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22948 q selected
    | true =>
      simp only [d228846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22949 q selected
    | true =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228852 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228894 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22954 (p : Pattern) (selected : d228895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22949 q selected
    | true =>
      simp only [d228850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228856 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228857 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228858 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22955 (p : Pattern) (selected : d228904 p = 1) : d231046 p = 1 := by
  have h0 (q : Pattern) (selected : d228780 q = 1) : d228780 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228789 q = 1) : d228789 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228810 q = 1) : d228810 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228860 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22950 q selected
    | true =>
      simp only [d228860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22951 q selected
  have h4 (q : Pattern) (selected : d228861 q = 1) : d231037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228861, d231037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228861, d231037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228876 q = 1) : d228876 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d228877 q = 1) : d231038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228877, d231038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228877, d231038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228878 q = 1) : d231039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228878, d231039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228878, d231039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228879 q = 1) : d231040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228879, d231040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228879, d231040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228886 q = 1) : d228886 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d228891 q = 1) : d228891 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d228893 q = 1) : d228893 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d228896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22953 q selected
    | true =>
      simp only [d228896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22954 q selected
  have h13 (q : Pattern) (selected : d228897 q = 1) : d231042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228897, d231042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228897, d231042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228900 q = 1) : d228900 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d228901 q = 1) : d231043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228901, d231043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228901, d231043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228902 q = 1) : d231044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228902, d231044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228902, d231044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228903 q = 1) : d231045 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228903, d231045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228903, d231045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228904 q = 1) : d231046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228904, d231046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228904, d231046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22956 (p : Pattern) (selected : d228924 p = 1) : d231053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228893 q = 1) : d228893 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22953 q selected
    | true =>
      simp only [d228896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22954 q selected
  have h3 (q : Pattern) (selected : d228897 q = 1) : d231042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228897, d231042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228897, d231042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228900 q = 1) : d228900 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228901 q = 1) : d231043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228901, d231043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228901, d231043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228922 q = 1) : d231051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228922, d231051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228922, d231051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228923 q = 1) : d231052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228923, d231052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228923, d231052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228924 q = 1) : d231053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228924, d231053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228924, d231053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22957 (p : Pattern) (selected : d229003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228989 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22942 q selected
  have h2 (q : Pattern) (selected : d228814 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22942 q selected
    | true =>
      simp only [d228814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228990 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228815 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228991 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228992 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228993 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
  have h8 (q : Pattern) (selected : d228820 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
    | true =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228994 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228821 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228995 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228996 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228997 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
  have h15 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d229000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d229001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d229002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d229003 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22958 (p : Pattern) (selected : d229005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228993 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
  have h2 (q : Pattern) (selected : d228820 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22943 q selected
    | true =>
      simp only [d228820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228994 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228821 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228995 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228996 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
  have h8 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229004 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229005 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22959 (p : Pattern) (selected : d229009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
  have h2 (q : Pattern) (selected : d228827 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22944 q selected
    | true =>
      simp only [d228827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228828 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229004 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229009 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22960 (p : Pattern) (selected : d229016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22957 q selected
    | true =>
      simp only [d229006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22958 q selected
  have h2 (q : Pattern) (selected : d229007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229010 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22958 q selected
    | true =>
      simp only [d229010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22959 q selected
  have h5 (q : Pattern) (selected : d229011 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229012 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229013 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22961 (p : Pattern) (selected : d229020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229010 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22958 q selected
    | true =>
      simp only [d229010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22959 q selected
  have h2 (q : Pattern) (selected : d229011 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229012 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229019 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229020 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22962 (p : Pattern) (selected : d229026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22960 q selected
    | true =>
      simp only [d229017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229021 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22961 q selected
    | true =>
      simp only [d229021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229022 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229023 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229024 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229025 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229026 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22963 (p : Pattern) (selected : d229030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229021 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22961 q selected
    | true =>
      simp only [d229021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229022 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229027 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229028 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22964 (p : Pattern) (selected : d229051 p = 1) : d231063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228988 q = 1) : d228988 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d229031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22962 q selected
    | true =>
      simp only [d229031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22963 q selected
  have h3 (q : Pattern) (selected : d229032 q = 1) : d231059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229032, d231059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229032, d231059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229047 q = 1) : d229047 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d229048 q = 1) : d231060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229048, d231060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229048, d231060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229049 q = 1) : d231061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229049, d231061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229049, d231061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229050 q = 1) : d231062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229050, d231062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229050, d231062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229051 q = 1) : d231063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229051, d231063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229051, d231063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22965 (p : Pattern) (selected : d229068 p = 1) : d231069 p = 1 := by
  have h0 (q : Pattern) (selected : d228772 q = 1) : d228772 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d228905 q = 1) : d231047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228905, d231047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22952 q selected
    | true =>
      simp only [d228905, d231047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22955 q selected
  have h2 (q : Pattern) (selected : d228918 q = 1) : d228918 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d228919 q = 1) : d231048 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228919, d231048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228919, d231048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d228920 q = 1) : d231049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228920, d231049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228920, d231049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228921 q = 1) : d231050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228921, d231050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228921, d231050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228925 q = 1) : d231054 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228925, d231054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228925, d231054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22956 q selected
  have h8 (q : Pattern) (selected : d228927 q = 1) : d228927 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d228928 q = 1) : d231055 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228928, d231055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228928, d231055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228929 q = 1) : d231056 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228929, d231056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228929, d231056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d228930 q = 1) : d231057 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228930, d231057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228930, d231057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d228931 q = 1) : d231058 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228931, d231058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228931, d231058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229052 q = 1) : d231064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229052, d231064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229052, d231064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22964 q selected
  have h14 (q : Pattern) (selected : d229063 q = 1) : d229063 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d229064 q = 1) : d231065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229064, d231065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229064, d231065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229065 q = 1) : d231066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229065, d231066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229065, d231066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d229066 q = 1) : d231067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229066, d231067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229066, d231067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d229067 q = 1) : d231068 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229067, d231068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d229067, d231068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d229068 q = 1) : d231069 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d229068, d231069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229068, d231069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22966 (p : Pattern) (selected : d229074 p = 1) : d231075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229069 q = 1) : d231070 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d229069, d231070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229069, d231070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22965 q selected
  have h2 (q : Pattern) (selected : d229070 q = 1) : d231071 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d229070, d231071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229070, d231071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229071 q = 1) : d231072 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d229071, d231072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229071, d231072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229072 q = 1) : d231073 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d229072, d231073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229072, d231073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229073 q = 1) : d231074 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d229073, d231074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229073, d231074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229074 q = 1) : d231075 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d229074, d231075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229074, d231075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22967 (p : Pattern) (selected : d229179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2197 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229178 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229179 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro22968 (p : Pattern) (selected : d229185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2197 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229178 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229185 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22969 (p : Pattern) (selected : d229192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2227 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229191 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d229191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229192 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d229192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22970 (p : Pattern) (selected : d229198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22967 q selected
    | true =>
      simp only [d229180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
    | true =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229190 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d229195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d229197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229198 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22971 (p : Pattern) (selected : d229200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
    | true =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229199 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229200 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22972 (p : Pattern) (selected : d229204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229199 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229204 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22973 (p : Pattern) (selected : d229211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229201 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22970 q selected
    | true =>
      simp only [d229201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22971 q selected
  have h2 (q : Pattern) (selected : d229202 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229203 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22971 q selected
    | true =>
      simp only [d229205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22972 q selected
  have h5 (q : Pattern) (selected : d229206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229209 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229210 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229211 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22974 (p : Pattern) (selected : d229215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22971 q selected
    | true =>
      simp only [d229205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22972 q selected
  have h2 (q : Pattern) (selected : d229206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229209 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229214 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229215 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22975 (p : Pattern) (selected : d229221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22973 q selected
    | true =>
      simp only [d229212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229216 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22974 q selected
    | true =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229217 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229218 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229219 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229221 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22976 (p : Pattern) (selected : d229225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229216 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22974 q selected
    | true =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229217 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229222 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229223 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229224 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229225 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22977 (p : Pattern) (selected : d229246 p = 1) : d231084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229153 q = 1) : d229153 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d229162 q = 1) : d229162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d229177 q = 1) : d229177 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d229226 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22975 q selected
    | true =>
      simp only [d229226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22976 q selected
  have h5 (q : Pattern) (selected : d229227 q = 1) : d231080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229227, d231080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229227, d231080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229242 q = 1) : d229242 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d229243 q = 1) : d231081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229243, d231081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229243, d231081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229244 q = 1) : d231082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229244, d231082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229244, d231082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229245 q = 1) : d231083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229245, d231083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229245, d231083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229246 q = 1) : d231084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229246, d231084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229246, d231084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22978 (p : Pattern) (selected : d229260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229212 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22973 q selected
    | true =>
      simp only [d229212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229213 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229216 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22974 q selected
    | true =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229217 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229218 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229219 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229220 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229260 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22979 (p : Pattern) (selected : d229261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229216 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22974 q selected
    | true =>
      simp only [d229216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229217 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229222 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229223 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229224 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229261 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22980 (p : Pattern) (selected : d229270 p = 1) : d231089 p = 1 := by
  have h0 (q : Pattern) (selected : d229153 q = 1) : d229153 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229162 q = 1) : d229162 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d229177 q = 1) : d229177 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d229226 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22975 q selected
    | true =>
      simp only [d229226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22976 q selected
  have h4 (q : Pattern) (selected : d229227 q = 1) : d231080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229227, d231080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229227, d231080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229242 q = 1) : d229242 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d229243 q = 1) : d231081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229243, d231081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229243, d231081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229244 q = 1) : d231082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229244, d231082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229244, d231082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229245 q = 1) : d231083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229245, d231083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229245, d231083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229252 q = 1) : d229252 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d229257 q = 1) : d229257 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d229259 q = 1) : d229259 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d229262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22978 q selected
    | true =>
      simp only [d229262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22979 q selected
  have h13 (q : Pattern) (selected : d229263 q = 1) : d231085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229263, d231085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229263, d231085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229266 q = 1) : d229266 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d229267 q = 1) : d231086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229267, d231086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229267, d231086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229268 q = 1) : d231087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229268, d231087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229268, d231087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229269 q = 1) : d231088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229269, d231088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229269, d231088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d229270 q = 1) : d231089 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229270, d231089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229270, d231089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22981 (p : Pattern) (selected : d229290 p = 1) : d231096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229259 q = 1) : d229259 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d229262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22978 q selected
    | true =>
      simp only [d229262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22979 q selected
  have h3 (q : Pattern) (selected : d229263 q = 1) : d231085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229263, d231085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229263, d231085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229266 q = 1) : d229266 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d229267 q = 1) : d231086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229267, d231086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229267, d231086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229288 q = 1) : d231094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229288, d231094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229288, d231094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229289 q = 1) : d231095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229289, d231095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229289, d231095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229290 q = 1) : d231096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229290, d231096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229290, d231096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22982 (p : Pattern) (selected : d229365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229351 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22967 q selected
  have h2 (q : Pattern) (selected : d229180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22967 q selected
    | true =>
      simp only [d229180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229352 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229353 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229354 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
  have h8 (q : Pattern) (selected : d229186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
    | true =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229360 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
  have h15 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d229361 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d229362 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d229363 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d229364 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d229365 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22983 (p : Pattern) (selected : d229367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
  have h2 (q : Pattern) (selected : d229186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22968 q selected
    | true =>
      simp only [d229186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229360 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
  have h8 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229361 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d229362 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d229363 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d229364 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d229367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22984 (p : Pattern) (selected : d229371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229360 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
  have h2 (q : Pattern) (selected : d229193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22969 q selected
    | true =>
      simp only [d229193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229361 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229362 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229363 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d229366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229371 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d229371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22985 (p : Pattern) (selected : d229378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229368 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22982 q selected
    | true =>
      simp only [d229368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22983 q selected
  have h2 (q : Pattern) (selected : d229369 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229370 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22983 q selected
    | true =>
      simp only [d229372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22984 q selected
  have h5 (q : Pattern) (selected : d229373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229376 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d229377 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229378 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22986 (p : Pattern) (selected : d229382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d229372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22983 q selected
    | true =>
      simp only [d229372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22984 q selected
  have h2 (q : Pattern) (selected : d229373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d229373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d229374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229376 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d229376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d229381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d229382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22987 (p : Pattern) (selected : d229388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229379 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22985 q selected
    | true =>
      simp only [d229379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229380 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22986 q selected
    | true =>
      simp only [d229383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229385 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229386 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d229387 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d229388 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22988 (p : Pattern) (selected : d229392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d229383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22986 q selected
    | true =>
      simp only [d229383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d229384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d229389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229390 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d229390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229391 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d229391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229392 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d229392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22989 (p : Pattern) (selected : d229413 p = 1) : d231106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229350 q = 1) : d229350 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d229393 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d229393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22987 q selected
    | true =>
      simp only [d229393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22988 q selected
  have h3 (q : Pattern) (selected : d229394 q = 1) : d231102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d229394, d231102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229394, d231102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229409 q = 1) : d229409 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d229410 q = 1) : d231103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d229410, d231103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229410, d231103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229411 q = 1) : d231104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d229411, d231104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229411, d231104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229412 q = 1) : d231105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d229412, d231105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229412, d231105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d229413 q = 1) : d231106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d229413, d231106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229413, d231106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22990 (p : Pattern) (selected : d229430 p = 1) : d231112 p = 1 := by
  have h0 (q : Pattern) (selected : d229145 q = 1) : d229145 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229271 q = 1) : d231090 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229271, d231090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22977 q selected
    | true =>
      simp only [d229271, d231090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22980 q selected
  have h2 (q : Pattern) (selected : d229284 q = 1) : d229284 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d229285 q = 1) : d231091 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229285, d231091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229285, d231091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d229286 q = 1) : d231092 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229286, d231092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229286, d231092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229287 q = 1) : d231093 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229287, d231093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229287, d231093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229291 q = 1) : d231097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229291, d231097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229291, d231097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22981 q selected
  have h8 (q : Pattern) (selected : d229293 q = 1) : d229293 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d229294 q = 1) : d231098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229294, d231098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d229294, d231098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229295 q = 1) : d231099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229295, d231099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d229295, d231099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d229296 q = 1) : d231100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229296, d231100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229296, d231100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d229297 q = 1) : d231101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229297, d231101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229297, d231101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229414 q = 1) : d231107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d229414, d231107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229414, d231107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22989 q selected
  have h14 (q : Pattern) (selected : d229425 q = 1) : d229425 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d229426 q = 1) : d231108 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d229426, d231108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d229426, d231108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229427 q = 1) : d231109 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d229427, d231109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229427, d231109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d229428 q = 1) : d231110 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d229428, d231110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d229428, d231110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d229429 q = 1) : d231111 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d229429, d231111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d229429, d231111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d229430 q = 1) : d231112 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d229430, d231112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d229430, d231112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22991 (p : Pattern) (selected : d229436 p = 1) : d231118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229431 q = 1) : d231113 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d229431, d231113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229431, d231113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22990 q selected
  have h2 (q : Pattern) (selected : d229432 q = 1) : d231114 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d229432, d231114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229432, d231114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d229433 q = 1) : d231115 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d229433, d231115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229433, d231115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d229434 q = 1) : d231116 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d229434, d231116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229434, d231116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d229435 q = 1) : d231117 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d229435, d231117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229435, d231117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229436 q = 1) : d231118 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d229436, d231118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d229436, d231118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22992 (p : Pattern) (selected : d229442 p = 1) : d231124 p = 1 := by
  have h0 (q : Pattern) (selected : d228111 q = 1) : d230953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228111, d230953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22885 q selected
    | true =>
      simp only [d228111, d230953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22899 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d228390 q = 1) : d230993 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228390, d230993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228390, d230993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22918 q selected
  have h3 (q : Pattern) (selected : d228391 q = 1) : d230994 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d228391, d230994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228391, d230994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228702 q = 1) : d231034 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d228702, d231034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228702, d231034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22941 q selected
  have h5 (q : Pattern) (selected : d228703 q = 1) : d231035 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d228703, d231035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228703, d231035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228704 q = 1) : d231036 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d228704, d231036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228704, d231036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d229075 q = 1) : d231076 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d229075, d231076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229075, d231076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22966 q selected
  have h8 (q : Pattern) (selected : d229076 q = 1) : d231077 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d229076, d231077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229076, d231077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d229077 q = 1) : d231078 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d229077, d231078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229077, d231078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d229078 q = 1) : d231079 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d229078, d231079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d229078, d231079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d229437 q = 1) : d231119 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d229437, d231119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229437, d231119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22991 q selected
  have h12 (q : Pattern) (selected : d229438 q = 1) : d231120 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d229438, d231120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229438, d231120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d229439 q = 1) : d231121 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d229439, d231121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229439, d231121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d229440 q = 1) : d231122 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d229440, d231122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229440, d231122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d229441 q = 1) : d231123 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d229441, d231123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d229441, d231123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d229442 q = 1) : d231124 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d229442, d231124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d229442, d231124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22993 (p : Pattern) (selected : d229448 p = 1) : d231130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229443 q = 1) : d231125 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d229443, d231125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22992 q selected
    | true =>
      simp only [d229443, d231125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229444 q = 1) : d231126 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d229444, d231126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229444, d231126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229445 q = 1) : d231127 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d229445, d231127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229445, d231127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229446 q = 1) : d231128 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d229446, d231128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229446, d231128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229447 q = 1) : d231129 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d229447, d231129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229447, d231129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229448 q = 1) : d231130 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d229448, d231130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229448, d231130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22994 (p : Pattern) (selected : d229454 p = 1) : d231136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229449 q = 1) : d231131 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d229449, d231131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22993 q selected
    | true =>
      simp only [d229449, d231131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229450 q = 1) : d231132 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d229450, d231132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229450, d231132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229451 q = 1) : d231133 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d229451, d231133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229451, d231133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229452 q = 1) : d231134 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d229452, d231134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229452, d231134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229453 q = 1) : d231135 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d229453, d231135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229453, d231135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229454 q = 1) : d231136 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d229454, d231136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229454, d231136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22995 (p : Pattern) (selected : d229459 p = 1) : d231141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229455 q = 1) : d231137 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d229455, d231137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22994 q selected
    | true =>
      simp only [d229455, d231137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229456 q = 1) : d231138 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d229456, d231138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229456, d231138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229457 q = 1) : d231139 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d229457, d231139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229457, d231139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229458 q = 1) : d231140 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d229458, d231140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229458, d231140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229459 q = 1) : d231141 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d229459, d231141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229459, d231141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22996 (p : Pattern) (selected : d229465 p = 1) : d231147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229460 q = 1) : d231142 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d229460, d231142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22995 q selected
    | true =>
      simp only [d229460, d231142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229461 q = 1) : d231143 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d229461, d231143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229461, d231143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229462 q = 1) : d231144 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d229462, d231144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229462, d231144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229463 q = 1) : d231145 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d229463, d231145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229463, d231145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229464 q = 1) : d231146 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d229464, d231146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229464, d231146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229465 q = 1) : d231147 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d229465, d231147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229465, d231147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22997 (p : Pattern) (selected : d229471 p = 1) : d231153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229466 q = 1) : d231148 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d229466, d231148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22996 q selected
    | true =>
      simp only [d229466, d231148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229467 q = 1) : d231149 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d229467, d231149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229467, d231149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229468 q = 1) : d231150 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d229468, d231150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229468, d231150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229469 q = 1) : d231151 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d229469, d231151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229469, d231151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229470 q = 1) : d231152 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d229470, d231152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229470, d231152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229471 q = 1) : d231153 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d229471, d231153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229471, d231153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22998 (p : Pattern) (selected : d229477 p = 1) : d231159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229472 q = 1) : d231154 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d229472, d231154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22997 q selected
    | true =>
      simp only [d229472, d231154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229473 q = 1) : d231155 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d229473, d231155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229473, d231155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229474 q = 1) : d231156 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d229474, d231156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229474, d231156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229475 q = 1) : d231157 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d229475, d231157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229475, d231157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229476 q = 1) : d231158 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d229476, d231158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229476, d231158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229477 q = 1) : d231159 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d229477, d231159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229477, d231159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22999 (p : Pattern) (selected : d229483 p = 1) : d231165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d229478 q = 1) : d231160 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d229478, d231160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22998 q selected
    | true =>
      simp only [d229478, d231160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d229479 q = 1) : d231161 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d229479, d231161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d229479, d231161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d229480 q = 1) : d231162 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d229480, d231162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d229480, d231162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d229481 q = 1) : d231163 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d229481, d231163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d229481, d231163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d229482 q = 1) : d231164 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d229482, d231164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d229482, d231164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d229483 q = 1) : d231165 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d229483, d231165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229483, d231165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
