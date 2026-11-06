import NetHack.Soko22Hazard87.AndIntroBlocks0325
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro81500 (p : Pattern) (ha : d307164 p = 1) (hb : d311877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307151 q = 1) (hb : d311864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307151, d311864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81497 q ha hb
    | true =>
      simp only [d307151, d311864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307152 q = 1) (hb : d311865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307152, d311865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307152, d311865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307159 q = 1) (hb : d311872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307159, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81499 q ha hb
    | true =>
      simp only [d307159, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307160 q = 1) (hb : d311873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307160, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307160, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307161 q = 1) (hb : d311874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307161, d311874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307161, d311874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307162 q = 1) (hb : d311875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307162, d311875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307162, d311875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307163 q = 1) (hb : d311876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307163, d311876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307163, d311876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307164 q = 1) (hb : d311877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307164, d311877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307164, d311877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81501 (p : Pattern) (ha : d307172 p = 1) (hb : d311880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307129 q = 1) (hb : d311842 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307129, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307129, d311842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81451 q ha hb
  have h2 (q : Pattern) (ha : d306876 q = 1) (hb : d311595 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d306876, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81451 q ha hb
    | true =>
      simp only [d306876, d311595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307130 q = 1) (hb : d311843 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307130, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307130, d311843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306877 q = 1) (hb : d311596 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d306877, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d306877, d311596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307131 q = 1) (hb : d311844 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307131, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307131, d311844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307132 q = 1) (hb : d311845 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307132, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307132, d311845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307138 q = 1) (hb : d311851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307138, d311851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307138, d311851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307172 q = 1) (hb : d311880 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307172, d311880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307172, d311880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81502 (p : Pattern) (ha : d307178 p = 1) (hb : d311886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307135 q = 1) (hb : d311848 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307135, d311848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81492 q ha hb
    | true =>
      simp only [d307135, d311848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81494 q ha hb
  have h2 (q : Pattern) (ha : d307136 q = 1) (hb : d311849 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307136, d311849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307136, d311849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307137 q = 1) (hb : d311850 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307137, d311850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307137, d311850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307140 q = 1) (hb : d311853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307140, d311853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81494 q ha hb
    | true =>
      simp only [d307140, d311853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81495 q ha hb
  have h5 (q : Pattern) (ha : d307141 q = 1) (hb : d311854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307141, d311854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307141, d311854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307142 q = 1) (hb : d311855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307142, d311855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307142, d311855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307143 q = 1) (hb : d311856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307143, d311856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307143, d311856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307173 q = 1) (hb : d311881 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307173, d311881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81494 q ha hb
    | true =>
      simp only [d307173, d311881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81501 q ha hb
  have h9 (q : Pattern) (ha : d307174 q = 1) (hb : d311882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307174, d311882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307174, d311882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307175 q = 1) (hb : d311883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307175, d311883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307175, d311883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307176 q = 1) (hb : d311884 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307176, d311884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307176, d311884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307177 q = 1) (hb : d311885 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307177, d311885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307177, d311885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307178 q = 1) (hb : d311886 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307178, d311886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307178, d311886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro81503 (p : Pattern) (ha : d307184 p = 1) (hb : d311892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307179 q = 1) (hb : d311887 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307179, d311887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81502 q ha hb
    | true =>
      simp only [d307179, d311887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307180 q = 1) (hb : d311888 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307180, d311888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307180, d311888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307181 q = 1) (hb : d311889 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307181, d311889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307181, d311889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307182 q = 1) (hb : d311890 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307182, d311890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307182, d311890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307183 q = 1) (hb : d311891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307183, d311891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307183, d311891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307184 q = 1) (hb : d311892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307184, d311892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307184, d311892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81504 (p : Pattern) (ha : d307190 p = 1) (hb : d311898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307165 q = 1) (hb : d311878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307165, d311878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81498 q ha hb
    | true =>
      simp only [d307165, d311878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81500 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307170 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d311879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d311879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307171, d311879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307185 q = 1) (hb : d311893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307185, d311893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81503 q ha hb
    | true =>
      simp only [d307185, d311893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307186 q = 1) (hb : d311894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307186, d311894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307186, d311894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307187 q = 1) (hb : d311895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d311895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d311895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307188 q = 1) (hb : d311896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d311896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d311896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307189 q = 1) (hb : d311897 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d311897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d311897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307190 q = 1) (hb : d311898 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d311898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d311898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81505 (p : Pattern) (ha : d307169 p = 1) (hb : d311903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307159 q = 1) (hb : d311872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307159, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81499 q ha hb
    | true =>
      simp only [d307159, d311872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307160 q = 1) (hb : d311873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307160, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307160, d311873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307166 q = 1) (hb : d311900 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307166, d311900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307166, d311900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307167 q = 1) (hb : d311901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307167, d311901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307167, d311901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307168 q = 1) (hb : d311902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307168, d311902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307168, d311902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307169 q = 1) (hb : d311903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307169, d311903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307169, d311903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81506 (p : Pattern) (ha : d307197 p = 1) (hb : d311909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307192 q = 1) (hb : d311904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307192, d311904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81505 q ha hb
    | true =>
      simp only [d307192, d311904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307193 q = 1) (hb : d311905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307193, d311905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307193, d311905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307194 q = 1) (hb : d311906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307194, d311906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307194, d311906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307195 q = 1) (hb : d311907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307195, d311907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307195, d311907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307196 q = 1) (hb : d311908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307196, d311908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307196, d311908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307197 q = 1) (hb : d311909 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307197, d311909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307197, d311909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81507 (p : Pattern) (ha : d307203 p = 1) (hb : d311915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306915 q = 1) (hb : d311634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306915, d311634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306915, d311634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81458 q ha hb
  have h2 (q : Pattern) (ha : d306916 q = 1) (hb : d311635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306916, d311635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306916, d311635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d306925 q = 1) (hb : d311644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306925, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81458 q ha hb
    | true =>
      simp only [d306925, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81461 q ha hb
  have h4 (q : Pattern) (ha : d306926 q = 1) (hb : d311645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306926, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306926, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d306927 q = 1) (hb : d311646 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306927, d311646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d306927, d311646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307050 q = 1) (hb : d311763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d311763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81479 q ha hb
    | true =>
      simp only [d307050, d311763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81486 q ha hb
  have h7 (q : Pattern) (ha : d307063 q = 1) (hb : d311776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307063, d311776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81487 q ha hb
    | true =>
      simp only [d307063, d311776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81488 q ha hb
  have h8 (q : Pattern) (ha : d307064 q = 1) (hb : d311777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d311777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307064, d311777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307065 q = 1) (hb : d311778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d311778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307065, d311778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307066 q = 1) (hb : d311779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d311779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307066, d311779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307070 q = 1) (hb : d311783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d311783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307070, d311783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81489 q ha hb
  have h12 (q : Pattern) (ha : d307072 q = 1) (hb : d311785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307072, d311785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307072, d311785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81490 q ha hb
  have h13 (q : Pattern) (ha : d307073 q = 1) (hb : d311786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d311786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307073, d311786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307074 q = 1) (hb : d311787 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d311787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307074, d311787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307075 q = 1) (hb : d311788 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d311788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307075, d311788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307076 q = 1) (hb : d311789 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d311789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307076, d311789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307191 q = 1) (hb : d311899 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d311899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307191, d311899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81504 q ha hb
  have h18 (q : Pattern) (ha : d307198 q = 1) (hb : d311910 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307198, d311910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307198, d311910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81506 q ha hb
  have h19 (q : Pattern) (ha : d307199 q = 1) (hb : d311911 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d311911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307199, d311911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307200 q = 1) (hb : d311912 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d311912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307200, d311912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307201 q = 1) (hb : d311913 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d311913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307201, d311913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307202 q = 1) (hb : d311914 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d311914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307202, d311914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307203 q = 1) (hb : d311915 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d311915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307203, d311915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro81508 (p : Pattern) (ha : d307209 p = 1) (hb : d311921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d311916 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d311916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d311916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81507 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d311917 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d311917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d311917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d311918 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d311918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d311918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d311919 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d311919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d311919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d311920 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d311920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d311920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d311921 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d311921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d311921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81509 (p : Pattern) (ha : d307222 p = 1) (hb : d311068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d53280 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262896 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2002 q = 1) (hb : d306331 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d306331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, d306331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42592 q = 1) (hb : d306332 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d306332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42592, d306332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d307221 q = 1) (hb : d311067 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d307221, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d307221, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d307222 q = 1) (hb : d311068 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d307222, d311068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307222, d311068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81510 (p : Pattern) (ha : d307226 p = 1) (hb : d311930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42592 q = 1) (hb : d306332 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d306332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42592, d306332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307221 q = 1) (hb : d311067 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d307221, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d307221, d311067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d307226 q = 1) (hb : d311930 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d307226, d311930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307226, d311930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro81511 (p : Pattern) (ha : d307232 p = 1) (hb : d311936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34783 q = 1) (hb : d307215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d307216 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
    | true =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d307217 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d307218 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307219 q = 1) (hb : d311925 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d307220 q = 1) (hb : d311926 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307223 q = 1) (hb : d311927 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68439 q hb ha
  have h11 (q : Pattern) (ha : d307224 q = 1) (hb : d311928 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307225 q = 1) (hb : d311929 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307229 q = 1) (hb : d311933 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307229, d311933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307229, d311933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307230 q = 1) (hb : d311934 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307230, d311934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307230, d311934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307231 q = 1) (hb : d311935 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307231, d311935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307231, d311935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307232 q = 1) (hb : d311936 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307232, d311936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307232, d311936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81512 (p : Pattern) (ha : d43867 p = 1) (hb : d307237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d53280 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2002 q = 1) (hb : d53281 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, d53281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2005 q = 1) (hb : d53284 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, d53284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2006 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2006, d53285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43867 q = 1) (hb : d307237 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43867, d307237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43867, d307237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81513 (p : Pattern) (ha : d307244 p = 1) (hb : d311674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d53280 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, d53280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262896 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2002 q = 1) (hb : d306331 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, d306331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, d306331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d34366 q = 1) (hb : d262896 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, d262896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34366, d262896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d34367 q = 1) (hb : d307243 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d34367, d307243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34367, d307243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307244 q = 1) (hb : d311674 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d307244, d311674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307244, d311674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro81514 (p : Pattern) (ha : d307250 p = 1) (hb : d311949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307223 q = 1) (hb : d311927 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68439 q hb ha
  have h5 (q : Pattern) (ha : d307224 q = 1) (hb : d311928 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d307225 q = 1) (hb : d311929 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43868 q = 1) (hb : d307238 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d307238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81512 q ha hb
    | true =>
      simp only [d43868, d307238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d43869 q = 1) (hb : d307239 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d307239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43869, d307239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d307240 q = 1) (hb : d311941 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307240, d311941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d307240, d311941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307241 q = 1) (hb : d311942 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307241, d311942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307241, d311942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307242 q = 1) (hb : d311943 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307242, d311943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307242, d311943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d307245 q = 1) (hb : d311944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h15 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h16 (q : Pattern) (ha : d307246 q = 1) (hb : d311945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d307247 q = 1) (hb : d311946 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d307248 q = 1) (hb : d311947 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d307249 q = 1) (hb : d311948 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h20 (q : Pattern) (ha : d307250 q = 1) (hb : d311949 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307250, d311949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307250, d311949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro81515 (p : Pattern) (ha : d307261 p = 1) (hb : d311958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307256 q = 1) (hb : d311675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d307257 q = 1) (hb : d311676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d307258 q = 1) (hb : d311955 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307258, d311955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307258, d311955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307259 q = 1) (hb : d311956 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307259, d311956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307259, d311956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d307260 q = 1) (hb : d311957 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307260, d311957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307260, d311957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d307245 q = 1) (hb : d311944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h10 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h11 (q : Pattern) (ha : d307246 q = 1) (hb : d311945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d307247 q = 1) (hb : d311946 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307248 q = 1) (hb : d311947 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d307249 q = 1) (hb : d311948 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h17 (q : Pattern) (ha : d307261 q = 1) (hb : d311958 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307261, d311958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307261, d311958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro81516 (p : Pattern) (ha : d34823 p = 1) (hb : d263191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d52964 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1084 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1524 q = 1) (hb : d52965 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1524, d52965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1524, d52965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1525 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1525, d52966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1525, d52966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d34823 q = 1) (hb : d263191 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d34823, d263191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34823, d263191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81517 (p : Pattern) (ha : d307272 p = 1) (hb : d311969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d307266 q = 1) (hb : d311963 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81516 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d307267 q = 1) (hb : d311964 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d307268 q = 1) (hb : d311965 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307268, d311965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307268, d311965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307269 q = 1) (hb : d311966 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307269, d311966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307269, d311966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d307270 q = 1) (hb : d311967 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307270, d311967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307270, d311967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307271 q = 1) (hb : d311968 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307271, d311968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307271, d311968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h11 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h12 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d1577 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d32178 q = 1) (hb : d242991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d32179 q = 1) (hb : d242992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d307272 q = 1) (hb : d311969 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307272, d311969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307272, d311969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro81518 (p : Pattern) (ha : d307278 p = 1) (hb : d311975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307233 q = 1) (hb : d311937 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307233, d311937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81511 q ha hb
    | true =>
      simp only [d307233, d311937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307234 q = 1) (hb : d311938 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307234, d311938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307234, d311938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307235 q = 1) (hb : d311939 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307235, d311939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307235, d311939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307236 q = 1) (hb : d311940 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307236, d311940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307236, d311940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307251 q = 1) (hb : d311950 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307251, d311950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81514 q ha hb
    | true =>
      simp only [d307251, d311950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307252 q = 1) (hb : d311951 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307252, d311951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307252, d311951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307253 q = 1) (hb : d311952 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307253, d311952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307253, d311952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307254 q = 1) (hb : d311953 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307254, d311953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307254, d311953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307255 q = 1) (hb : d311954 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307255, d311954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307255, d311954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307262 q = 1) (hb : d311959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
    | true =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307263 q = 1) (hb : d311960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307264 q = 1) (hb : d311961 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307264, d311961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307264, d311961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307265 q = 1) (hb : d311962 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307265, d311962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307265, d311962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307275 q = 1) (hb : d311972 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307276 q = 1) (hb : d311973 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307277 q = 1) (hb : d311974 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307277, d311974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307277, d311974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307278 q = 1) (hb : d311975 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307278, d311975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307278, d311975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81519 (p : Pattern) (ha : d307285 p = 1) (hb : d311982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307223 q = 1) (hb : d311927 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307223, d311927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68439 q hb ha
  have h5 (q : Pattern) (ha : d307224 q = 1) (hb : d311928 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307224, d311928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d307225 q = 1) (hb : d311929 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307225, d311929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43868 q = 1) (hb : d307238 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43868, d307238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81512 q ha hb
    | true =>
      simp only [d43868, d307238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d43869 q = 1) (hb : d307239 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43869, d307239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43869, d307239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d307240 q = 1) (hb : d311941 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307240, d311941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d307240, d311941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307241 q = 1) (hb : d311942 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307241, d311942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307241, d311942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307242 q = 1) (hb : d311943 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307242, d311943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307242, d311943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d307266 q = 1) (hb : d311963 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81516 q hb ha
  have h15 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h16 (q : Pattern) (ha : d307267 q = 1) (hb : d311964 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d307279 q = 1) (hb : d311976 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h18 (q : Pattern) (ha : d307280 q = 1) (hb : d311977 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d307281 q = 1) (hb : d311978 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h21 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h22 (q : Pattern) (ha : d307282 q = 1) (hb : d311979 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d307283 q = 1) (hb : d311980 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d307284 q = 1) (hb : d311981 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h25 (q : Pattern) (ha : d307285 q = 1) (hb : d311982 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307285, d311982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307285, d311982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro81520 (p : Pattern) (ha : d307290 p = 1) (hb : d311987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d307266 q = 1) (hb : d311963 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81516 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d307267 q = 1) (hb : d311964 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307279 q = 1) (hb : d311976 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h5 (q : Pattern) (ha : d307280 q = 1) (hb : d311977 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d307281 q = 1) (hb : d311978 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d307282 q = 1) (hb : d311979 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d307283 q = 1) (hb : d311980 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307284 q = 1) (hb : d311981 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h15 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h16 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1577 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h18 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d32178 q = 1) (hb : d242991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d32178, d242991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d32179 q = 1) (hb : d242992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d32179, d242992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d307290 q = 1) (hb : d311987 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307290, d311987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307290, d311987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  exact h24 p ha hb
theorem andIntro81521 (p : Pattern) (ha : d307297 p = 1) (hb : d311994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307286 q = 1) (hb : d311983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
    | true =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307287 q = 1) (hb : d311984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307288 q = 1) (hb : d311985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307288, d311985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307288, d311985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307289 q = 1) (hb : d311986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307289, d311986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307289, d311986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307293 q = 1) (hb : d311990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307294 q = 1) (hb : d311991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307295 q = 1) (hb : d311992 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307295, d311992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307295, d311992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307275 q = 1) (hb : d311972 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307276 q = 1) (hb : d311973 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307296 q = 1) (hb : d311993 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307296, d311993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307296, d311993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307297 q = 1) (hb : d311994 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307297, d311994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307297, d311994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81522 (p : Pattern) (ha : d307302 p = 1) (hb : d311999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307293 q = 1) (hb : d311990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307294 q = 1) (hb : d311991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307301 q = 1) (hb : d311998 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307301, d311998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307301, d311998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d307302 q = 1) (hb : d311999 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307302, d311999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307302, d311999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro81523 (p : Pattern) (ha : d307309 p = 1) (hb : d312006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307298 q = 1) (hb : d311995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81518 q ha hb
    | true =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
  have h2 (q : Pattern) (ha : d307299 q = 1) (hb : d311996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307300 q = 1) (hb : d311997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307303 q = 1) (hb : d312000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
    | true =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81522 q ha hb
  have h5 (q : Pattern) (ha : d307304 q = 1) (hb : d312001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307305 q = 1) (hb : d312002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307306 q = 1) (hb : d312003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307307 q = 1) (hb : d312004 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307307, d312004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307307, d312004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307308 q = 1) (hb : d312005 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307308, d312005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307308, d312005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307309 q = 1) (hb : d312006 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307309, d312006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307309, d312006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro81524 (p : Pattern) (ha : d307313 p = 1) (hb : d312010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307303 q = 1) (hb : d312000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
    | true =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81522 q ha hb
  have h2 (q : Pattern) (ha : d307304 q = 1) (hb : d312001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307305 q = 1) (hb : d312002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307307 q = 1) (hb : d312004 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307307, d312004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307307, d312004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307312 q = 1) (hb : d312009 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307312, d312009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307312, d312009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307313 q = 1) (hb : d312010 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307313, d312010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307313, d312010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81525 (p : Pattern) (ha : d307319 p = 1) (hb : d312016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307317 q = 1) (hb : d312014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307318 q = 1) (hb : d312015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307318, d312015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307318, d312015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307319 q = 1) (hb : d312016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307319, d312016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307319, d312016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81526 (p : Pattern) (ha : d307323 p = 1) (hb : d312020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307321 q = 1) (hb : d312018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307322 q = 1) (hb : d312019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307322, d312019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307322, d312019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307323 q = 1) (hb : d312020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307323, d312020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307323, d312020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81527 (p : Pattern) (ha : d307329 p = 1) (hb : d312026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307324 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
    | true =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
  have h2 (q : Pattern) (ha : d307325 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307326 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307327 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307328 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307329 q = 1) (hb : d312026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307329, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307329, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81528 (p : Pattern) (ha : d307332 p = 1) (hb : d312029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307317 q = 1) (hb : d312014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307318 q = 1) (hb : d312015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307318, d312015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307318, d312015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307332 q = 1) (hb : d312029 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307332, d312029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307332, d312029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81529 (p : Pattern) (ha : d307333 p = 1) (hb : d312030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307321 q = 1) (hb : d312018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307322 q = 1) (hb : d312019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307322, d312019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307322, d312019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307333 q = 1) (hb : d312030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307333, d312030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307333, d312030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81530 (p : Pattern) (ha : d307339 p = 1) (hb : d312036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307324 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
    | true =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
  have h2 (q : Pattern) (ha : d307325 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307326 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307327 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307328 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307334 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81528 q ha hb
    | true =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81529 q ha hb
  have h7 (q : Pattern) (ha : d307335 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307335, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307335, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307336 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307336, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307336, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307337 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307337, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307337, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307338 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307338, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307338, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307339 q = 1) (hb : d312036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307339, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307339, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81531 (p : Pattern) (ha : d307344 p = 1) (hb : d312041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307317 q = 1) (hb : d312014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307343 q = 1) (hb : d312040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307343, d312040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307343, d312040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307344 q = 1) (hb : d312041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307344, d312041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307344, d312041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81532 (p : Pattern) (ha : d307346 p = 1) (hb : d312043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307321 q = 1) (hb : d312018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307345 q = 1) (hb : d312042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307345, d312042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307345, d312042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307346 q = 1) (hb : d312043 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307346, d312043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307346, d312043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81533 (p : Pattern) (ha : d307353 p = 1) (hb : d312050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307351 q = 1) (hb : d312048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307351, d312048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307351, d312048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307352 q = 1) (hb : d312049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307352, d312049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307352, d312049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307353 q = 1) (hb : d312050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307353, d312050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307353, d312050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81534 (p : Pattern) (ha : d307356 p = 1) (hb : d312053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307354 q = 1) (hb : d312051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307354, d312051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307354, d312051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307355 q = 1) (hb : d312052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307355, d312052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307355, d312052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307356 q = 1) (hb : d312053 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307356, d312053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307356, d312053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81535 (p : Pattern) (ha : d307360 p = 1) (hb : d312057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34783 q = 1) (hb : d307215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d307216 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
    | true =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d307217 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d307218 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307219 q = 1) (hb : d311925 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d307220 q = 1) (hb : d311926 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307360 q = 1) (hb : d312057 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307360, d312057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307360, d312057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81536 (p : Pattern) (ha : d307368 p = 1) (hb : d312062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34783 q = 1) (hb : d307215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34783, d307215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43846 q = 1) (hb : d307216 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
    | true =>
      simp only [d43846, d307216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43847 q = 1) (hb : d307217 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43847, d307217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43848 q = 1) (hb : d307218 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43848, d307218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307219 q = 1) (hb : d311925 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307219, d311925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d307220 q = 1) (hb : d311926 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307220, d311926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306598 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d307256 q = 1) (hb : d311675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307257 q = 1) (hb : d311676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307365 q = 1) (hb : d311686 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307365, d311686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307365, d311686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307366 q = 1) (hb : d311687 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307366, d311687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307366, d311687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307367 q = 1) (hb : d311688 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307367, d311688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307367, d311688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307368 q = 1) (hb : d312062 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307368, d312062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307368, d312062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro81537 (p : Pattern) (ha : d307376 p = 1) (hb : d312068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307375 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307256 q = 1) (hb : d311675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307256, d311675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307257 q = 1) (hb : d311676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307257, d311676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d307365 q = 1) (hb : d311686 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307365, d311686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307365, d311686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307366 q = 1) (hb : d311687 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307366, d311687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307366, d311687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d307367 q = 1) (hb : d311688 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307367, d311688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307367, d311688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d307376 q = 1) (hb : d312068 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307376, d312068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307376, d312068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81538 (p : Pattern) (ha : d307382 p = 1) (hb : d312074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307361 q = 1) (hb : d312058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307361, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81535 q ha hb
    | true =>
      simp only [d307361, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307362 q = 1) (hb : d312059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307362, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307362, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307363 q = 1) (hb : d312060 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307363, d312060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307363, d312060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307364 q = 1) (hb : d312061 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307364, d312061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307364, d312061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307369 q = 1) (hb : d312063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307369, d312063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81536 q ha hb
    | true =>
      simp only [d307369, d312063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307370 q = 1) (hb : d312064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307370, d312064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307370, d312064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307371 q = 1) (hb : d312065 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307371, d312065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307371, d312065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307372 q = 1) (hb : d312066 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307372, d312066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307372, d312066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307373 q = 1) (hb : d312067 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307373, d312067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307373, d312067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307377 q = 1) (hb : d312069 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307377, d312069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81537 q ha hb
    | true =>
      simp only [d307377, d312069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307378 q = 1) (hb : d312070 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307378, d312070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307378, d312070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307379 q = 1) (hb : d312071 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307379, d312071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307379, d312071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307380 q = 1) (hb : d312072 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307380, d312072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307380, d312072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307262 q = 1) (hb : d311959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
    | true =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307263 q = 1) (hb : d311960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307264 q = 1) (hb : d311961 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307264, d311961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307264, d311961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307265 q = 1) (hb : d311962 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307265, d311962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307265, d311962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307381 q = 1) (hb : d312073 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307381, d312073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307381, d312073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307382 q = 1) (hb : d312074 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307382, d312074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307382, d312074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81539 (p : Pattern) (ha : d307391 p = 1) (hb : d312083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2008 q = 1) (hb : d307213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d307213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d34782 q = 1) (hb : d307214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34782, d307214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307386 q = 1) (hb : d312078 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307386, d312078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307386, d312078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q hb ha
  have h5 (q : Pattern) (ha : d307387 q = 1) (hb : d312079 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307387, d312079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307387, d312079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d307388 q = 1) (hb : d312080 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307388, d312080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307388, d312080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307389 q = 1) (hb : d312081 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307389, d312081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307389, d312081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d307390 q = 1) (hb : d312082 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307390, d312082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307390, d312082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d307245 q = 1) (hb : d311944 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81513 q ha hb
    | true =>
      simp only [d307245, d311944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61120 q hb ha
  have h10 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h11 (q : Pattern) (ha : d307246 q = 1) (hb : d311945 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307246, d311945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d307247 q = 1) (hb : d311946 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307247, d311946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307248 q = 1) (hb : d311947 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307248, d311947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h16 (q : Pattern) (ha : d307249 q = 1) (hb : d311948 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307249, d311948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h17 (q : Pattern) (ha : d307391 q = 1) (hb : d312083 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307391, d312083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307391, d312083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro81540 (p : Pattern) (ha : d307397 p = 1) (hb : d312089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307392 q = 1) (hb : d312084 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307392, d312084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81539 q ha hb
    | true =>
      simp only [d307392, d312084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307393 q = 1) (hb : d312085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307393, d312085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307393, d312085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307394 q = 1) (hb : d312086 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307394, d312086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307394, d312086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307395 q = 1) (hb : d312087 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307395, d312087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307395, d312087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307275 q = 1) (hb : d311972 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307275, d311972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307276 q = 1) (hb : d311973 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307276, d311973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307396 q = 1) (hb : d312088 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307396, d312088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307396, d312088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307296 q = 1) (hb : d311993 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307296, d311993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307296, d311993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307397 q = 1) (hb : d312089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307397, d312089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307397, d312089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81541 (p : Pattern) (ha : d307403 p = 1) (hb : d312095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307383 q = 1) (hb : d312075 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307383, d312075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81538 q ha hb
    | true =>
      simp only [d307383, d312075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81518 q ha hb
  have h2 (q : Pattern) (ha : d307384 q = 1) (hb : d312076 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307384, d312076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307384, d312076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307385 q = 1) (hb : d312077 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307385, d312077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307385, d312077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307398 q = 1) (hb : d312090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307398, d312090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81518 q ha hb
    | true =>
      simp only [d307398, d312090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81540 q ha hb
  have h5 (q : Pattern) (ha : d307399 q = 1) (hb : d312091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307399, d312091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307399, d312091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307400 q = 1) (hb : d312092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307400, d312092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307400, d312092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307401 q = 1) (hb : d312093 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307401, d312093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307401, d312093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307298 q = 1) (hb : d311995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81518 q ha hb
    | true =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
  have h9 (q : Pattern) (ha : d307299 q = 1) (hb : d311996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307300 q = 1) (hb : d311997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307303 q = 1) (hb : d312000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
    | true =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81522 q ha hb
  have h12 (q : Pattern) (ha : d307304 q = 1) (hb : d312001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307305 q = 1) (hb : d312002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307306 q = 1) (hb : d312003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307402 q = 1) (hb : d312094 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307402, d312094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307402, d312094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307403 q = 1) (hb : d312095 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307403, d312095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307403, d312095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro81542 (p : Pattern) (ha : d307409 p = 1) (hb : d312101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307404 q = 1) (hb : d312096 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307404, d312096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81541 q ha hb
    | true =>
      simp only [d307404, d312096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307405 q = 1) (hb : d312097 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307405, d312097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307405, d312097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307406 q = 1) (hb : d312098 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307406, d312098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307406, d312098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307407 q = 1) (hb : d312099 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307407, d312099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307407, d312099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307408 q = 1) (hb : d312100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307408, d312100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307408, d312100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307409 q = 1) (hb : d312101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307409, d312101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307409, d312101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81543 (p : Pattern) (ha : d307412 p = 1) (hb : d312104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d307266 q = 1) (hb : d311963 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81516 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d307267 q = 1) (hb : d311964 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d307268 q = 1) (hb : d311965 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307268, d311965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307268, d311965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307269 q = 1) (hb : d311966 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307269, d311966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307269, d311966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d307270 q = 1) (hb : d311967 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307270, d311967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307270, d311967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307271 q = 1) (hb : d311968 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307271, d311968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307271, d311968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h11 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d307412 q = 1) (hb : d312104 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307412, d312104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307412, d312104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  exact h18 p ha hb
theorem andIntro81544 (p : Pattern) (ha : d307418 p = 1) (hb : d312110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307286 q = 1) (hb : d311983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
    | true =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307287 q = 1) (hb : d311984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307288 q = 1) (hb : d311985 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307288, d311985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307288, d311985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307289 q = 1) (hb : d311986 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307289, d311986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307289, d311986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307293 q = 1) (hb : d311990 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307293, d311990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307294 q = 1) (hb : d311991 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307294, d311991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307295 q = 1) (hb : d311992 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307295, d311992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307295, d311992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307413 q = 1) (hb : d312105 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307413, d312105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81543 q ha hb
    | true =>
      simp only [d307413, d312105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307414 q = 1) (hb : d312106 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307414, d312106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307414, d312106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307415 q = 1) (hb : d312107 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307415, d312107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307415, d312107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307416 q = 1) (hb : d312108 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307416, d312108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307416, d312108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307417 q = 1) (hb : d312109 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307417, d312109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307417, d312109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307418 q = 1) (hb : d312110 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307418, d312110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307418, d312110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81545 (p : Pattern) (ha : d307419 p = 1) (hb : d312111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d307266 q = 1) (hb : d311963 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81509 q ha hb
    | true =>
      simp only [d307266, d311963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81516 q hb ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d242968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32155, d242968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h3 (q : Pattern) (ha : d307267 q = 1) (hb : d311964 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307267, d311964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307279 q = 1) (hb : d311976 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307279, d311976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q hb ha
  have h5 (q : Pattern) (ha : d307280 q = 1) (hb : d311977 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307280, d311977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d307281 q = 1) (hb : d311978 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307281, d311978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307227 q = 1) (hb : d311931 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81510 q ha hb
    | true =>
      simp only [d307227, d311931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d307228 q = 1) (hb : d311932 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307228, d311932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d307282 q = 1) (hb : d311979 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307282, d311979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d307283 q = 1) (hb : d311980 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307283, d311980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307284 q = 1) (hb : d311981 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307284, d311981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h15 (q : Pattern) (ha : d5129 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d307419 q = 1) (hb : d312111 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307419, d312111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307419, d312111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  exact h20 p ha hb
theorem andIntro81546 (p : Pattern) (ha : d307425 p = 1) (hb : d312117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307420 q = 1) (hb : d312112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307420, d312112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81545 q ha hb
    | true =>
      simp only [d307420, d312112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307421 q = 1) (hb : d312113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307421, d312113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307421, d312113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307422 q = 1) (hb : d312114 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307422, d312114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307422, d312114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307423 q = 1) (hb : d312115 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307423, d312115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307423, d312115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307424 q = 1) (hb : d312116 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307424, d312116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307424, d312116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307425 q = 1) (hb : d312117 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307425, d312117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307425, d312117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81547 (p : Pattern) (ha : d307431 p = 1) (hb : d312123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307298 q = 1) (hb : d311995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81518 q ha hb
    | true =>
      simp only [d307298, d311995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
  have h2 (q : Pattern) (ha : d307299 q = 1) (hb : d311996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307299, d311996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307300 q = 1) (hb : d311997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307300, d311997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307303 q = 1) (hb : d312000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81521 q ha hb
    | true =>
      simp only [d307303, d312000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81522 q ha hb
  have h5 (q : Pattern) (ha : d307304 q = 1) (hb : d312001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307304, d312001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307305 q = 1) (hb : d312002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307305, d312002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307306 q = 1) (hb : d312003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307306, d312003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307426 q = 1) (hb : d312118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307426, d312118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81544 q ha hb
    | true =>
      simp only [d307426, d312118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81546 q ha hb
  have h9 (q : Pattern) (ha : d307427 q = 1) (hb : d312119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307427, d312119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307427, d312119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307428 q = 1) (hb : d312120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307428, d312120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307428, d312120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307429 q = 1) (hb : d312121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307429, d312121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307429, d312121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307430 q = 1) (hb : d312122 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307430, d312122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307430, d312122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307431 q = 1) (hb : d312123 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307431, d312123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307431, d312123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro81548 (p : Pattern) (ha : d307437 p = 1) (hb : d312129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307432 q = 1) (hb : d312124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307432, d312124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81547 q ha hb
    | true =>
      simp only [d307432, d312124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307433 q = 1) (hb : d312125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307433, d312125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307433, d312125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307434 q = 1) (hb : d312126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307434, d312126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307434, d312126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307435 q = 1) (hb : d312127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307435, d312127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307435, d312127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307436 q = 1) (hb : d312128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307436, d312128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307436, d312128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307437 q = 1) (hb : d312129 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307437, d312129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307437, d312129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81549 (p : Pattern) (ha : d307443 p = 1) (hb : d312135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307347 q = 1) (hb : d312044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307347, d312044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81531 q ha hb
    | true =>
      simp only [d307347, d312044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81532 q ha hb
  have h2 (q : Pattern) (ha : d307348 q = 1) (hb : d312045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307348, d312045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307348, d312045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307349 q = 1) (hb : d312046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307349, d312046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307349, d312046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307350 q = 1) (hb : d312047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307350, d312047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307350, d312047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307357 q = 1) (hb : d312054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307357, d312054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81533 q ha hb
    | true =>
      simp only [d307357, d312054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81534 q ha hb
  have h6 (q : Pattern) (ha : d307358 q = 1) (hb : d312055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307358, d312055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307358, d312055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307359 q = 1) (hb : d312056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307359, d312056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307359, d312056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307410 q = 1) (hb : d312102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307410, d312102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81542 q ha hb
    | true =>
      simp only [d307410, d312102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d307411 q = 1) (hb : d312103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d312103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307411, d312103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d307438 q = 1) (hb : d312130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307438, d312130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81548 q ha hb
    | true =>
      simp only [d307438, d312130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307439 q = 1) (hb : d312131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307439, d312131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307439, d312131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307440 q = 1) (hb : d312132 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d312132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307440, d312132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307441 q = 1) (hb : d312133 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d312133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307441, d312133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307442 q = 1) (hb : d312134 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d312134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307442, d312134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307443 q = 1) (hb : d312135 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307443, d312135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307443, d312135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro81550 (p : Pattern) (ha : d307444 p = 1) (hb : d312136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307317 q = 1) (hb : d312014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307317, d312014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307343 q = 1) (hb : d312040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307343, d312040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307343, d312040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307444 q = 1) (hb : d312136 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307444, d312136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307444, d312136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81551 (p : Pattern) (ha : d307445 p = 1) (hb : d312137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307321 q = 1) (hb : d312018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307321, d312018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307345 q = 1) (hb : d312042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307345, d312042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307345, d312042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307445 q = 1) (hb : d312137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307445, d312137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307445, d312137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81552 (p : Pattern) (ha : d307450 p = 1) (hb : d312142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307316 q = 1) (hb : d312013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307316, d312013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307351 q = 1) (hb : d312048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307351, d312048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307351, d312048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307352 q = 1) (hb : d312049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307352, d312049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307352, d312049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307450 q = 1) (hb : d312142 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307450, d312142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307450, d312142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81553 (p : Pattern) (ha : d307451 p = 1) (hb : d312143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307314 q = 1) (hb : d312011 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81524 q ha hb
    | true =>
      simp only [d307314, d312011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307315 q = 1) (hb : d312012 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307315, d312012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307320 q = 1) (hb : d312017 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307320, d312017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307354 q = 1) (hb : d312051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307354, d312051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307354, d312051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307355 q = 1) (hb : d312052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307355, d312052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307355, d312052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307451 q = 1) (hb : d312143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307451, d312143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307451, d312143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81554 (p : Pattern) (ha : d307455 p = 1) (hb : d312147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307404 q = 1) (hb : d312096 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307404, d312096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81541 q ha hb
    | true =>
      simp only [d307404, d312096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307405 q = 1) (hb : d312097 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307405, d312097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307405, d312097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307310 q = 1) (hb : d312007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81523 q ha hb
    | true =>
      simp only [d307310, d312007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307311 q = 1) (hb : d312008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307311, d312008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307406 q = 1) (hb : d312098 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307406, d312098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307406, d312098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307407 q = 1) (hb : d312099 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307407, d312099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307407, d312099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307408 q = 1) (hb : d312100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307408, d312100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307408, d312100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307455 q = 1) (hb : d312147 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307455, d312147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307455, d312147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81555 (p : Pattern) (ha : d307458 p = 1) (hb : d312150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307432 q = 1) (hb : d312124 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307432, d312124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81547 q ha hb
    | true =>
      simp only [d307432, d312124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307433 q = 1) (hb : d312125 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307433, d312125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307433, d312125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307434 q = 1) (hb : d312126 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307434, d312126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307434, d312126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307435 q = 1) (hb : d312127 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307435, d312127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307435, d312127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307436 q = 1) (hb : d312128 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307436, d312128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307436, d312128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307458 q = 1) (hb : d312150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307458, d312150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307458, d312150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81556 (p : Pattern) (ha : d307464 p = 1) (hb : d312156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307347 q = 1) (hb : d312044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307347, d312044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81531 q ha hb
    | true =>
      simp only [d307347, d312044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81532 q ha hb
  have h2 (q : Pattern) (ha : d307348 q = 1) (hb : d312045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307348, d312045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307348, d312045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307349 q = 1) (hb : d312046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307349, d312046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307349, d312046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307350 q = 1) (hb : d312047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307350, d312047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307350, d312047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307357 q = 1) (hb : d312054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307357, d312054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81533 q ha hb
    | true =>
      simp only [d307357, d312054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81534 q ha hb
  have h6 (q : Pattern) (ha : d307358 q = 1) (hb : d312055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307358, d312055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307358, d312055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307359 q = 1) (hb : d312056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307359, d312056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307359, d312056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307410 q = 1) (hb : d312102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307410, d312102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81542 q ha hb
    | true =>
      simp only [d307410, d312102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d307411 q = 1) (hb : d312103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d312103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307411, d312103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d307438 q = 1) (hb : d312130 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307438, d312130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81548 q ha hb
    | true =>
      simp only [d307438, d312130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307439 q = 1) (hb : d312131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307439, d312131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307439, d312131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307440 q = 1) (hb : d312132 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d312132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307440, d312132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307441 q = 1) (hb : d312133 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d312133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307441, d312133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307442 q = 1) (hb : d312134 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d312134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307442, d312134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307446 q = 1) (hb : d312138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307446, d312138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81550 q ha hb
    | true =>
      simp only [d307446, d312138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81551 q ha hb
  have h17 (q : Pattern) (ha : d307447 q = 1) (hb : d312139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307447, d312139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307447, d312139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307448 q = 1) (hb : d312140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307448, d312140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307448, d312140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d307449 q = 1) (hb : d312141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307449, d312141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307449, d312141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307452 q = 1) (hb : d312144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307452, d312144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81552 q ha hb
    | true =>
      simp only [d307452, d312144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81553 q ha hb
  have h21 (q : Pattern) (ha : d307453 q = 1) (hb : d312145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307453, d312145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307453, d312145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d307454 q = 1) (hb : d312146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307454, d312146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307454, d312146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307456 q = 1) (hb : d312148 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307456, d312148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81554 q ha hb
    | true =>
      simp only [d307456, d312148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81528 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d307334 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d307457 q = 1) (hb : d312149 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d312149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d307457, d312149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d307459 q = 1) (hb : d312151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307459, d312151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81555 q ha hb
    | true =>
      simp only [d307459, d312151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d307460 q = 1) (hb : d312152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307460, d312152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d307460, d312152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d307461 q = 1) (hb : d312153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d312153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d307461, d312153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d307462 q = 1) (hb : d312154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307462, d312154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d307462, d312154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d307463 q = 1) (hb : d312155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307463, d312155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307463, d312155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d307464 q = 1) (hb : d312156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307464, d312156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307464, d312156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro81557 (p : Pattern) (ha : d307471 p = 1) (hb : d312163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307324 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
    | true =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
  have h2 (q : Pattern) (ha : d307325 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307325, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307326 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307326, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307327 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307327, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307328 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307328, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307466 q = 1) (hb : d312158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307466, d312158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
    | true =>
      simp only [d307466, d312158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307467 q = 1) (hb : d312159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307467, d312159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307467, d312159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307468 q = 1) (hb : d312160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307468, d312160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307468, d312160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307469 q = 1) (hb : d312161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307469, d312161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307469, d312161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307470 q = 1) (hb : d312162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307470, d312162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307470, d312162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307471 q = 1) (hb : d312163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307471, d312163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307471, d312163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81558 (p : Pattern) (ha : d307477 p = 1) (hb : d312169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307466 q = 1) (hb : d312158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307466, d312158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
    | true =>
      simp only [d307466, d312158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307467 q = 1) (hb : d312159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307467, d312159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307467, d312159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307468 q = 1) (hb : d312160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307468, d312160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307468, d312160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307469 q = 1) (hb : d312161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307469, d312161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307469, d312161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307470 q = 1) (hb : d312162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307470, d312162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307470, d312162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307472 q = 1) (hb : d312164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307472, d312164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81529 q ha hb
    | true =>
      simp only [d307472, d312164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307473 q = 1) (hb : d312165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307473, d312165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307473, d312165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307474 q = 1) (hb : d312166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307474, d312166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307474, d312166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307475 q = 1) (hb : d312167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307475, d312167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307475, d312167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307476 q = 1) (hb : d312168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307476, d312168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307476, d312168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307477 q = 1) (hb : d312169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307477, d312169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307477, d312169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro81559 (p : Pattern) (ha : d307484 p = 1) (hb : d312176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307456 q = 1) (hb : d312148 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307456, d312148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81554 q ha hb
    | true =>
      simp only [d307456, d312148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81528 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307334 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307457 q = 1) (hb : d312149 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d312149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307457, d312149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307459 q = 1) (hb : d312151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307459, d312151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81555 q ha hb
    | true =>
      simp only [d307459, d312151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307460 q = 1) (hb : d312152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307460, d312152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307460, d312152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307461 q = 1) (hb : d312153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d312153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307461, d312153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307482 q = 1) (hb : d312174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307482, d312174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307482, d312174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307483 q = 1) (hb : d312175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307483, d312175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307483, d312175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307484 q = 1) (hb : d312176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d312176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d312176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81560 (p : Pattern) (ha : d307486 p = 1) (hb : d312178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307472 q = 1) (hb : d312164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307472, d312164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81529 q ha hb
    | true =>
      simp only [d307472, d312164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307473 q = 1) (hb : d312165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307473, d312165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307473, d312165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307474 q = 1) (hb : d312166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307474, d312166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307474, d312166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307475 q = 1) (hb : d312167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307475, d312167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307475, d312167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307476 q = 1) (hb : d312168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307476, d312168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307476, d312168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307486 q = 1) (hb : d312178 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307486, d312178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307486, d312178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81561 (p : Pattern) (ha : d307510 p = 1) (hb : d312202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307492 q = 1) (hb : d312184 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307492, d312184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307492, d312184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81535 q ha hb
  have h2 (q : Pattern) (ha : d307361 q = 1) (hb : d312058 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307361, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81535 q ha hb
    | true =>
      simp only [d307361, d312058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307493 q = 1) (hb : d312185 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307493, d312185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307493, d312185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307362 q = 1) (hb : d312059 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307362, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307362, d312059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307494 q = 1) (hb : d312186 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307494, d312186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307494, d312186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307495 q = 1) (hb : d312187 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307495, d312187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307495, d312187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307496 q = 1) (hb : d312188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307496, d312188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307496, d312188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81536 q ha hb
  have h8 (q : Pattern) (ha : d307369 q = 1) (hb : d312063 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307369, d312063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81536 q ha hb
    | true =>
      simp only [d307369, d312063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307497 q = 1) (hb : d312189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307497, d312189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307497, d312189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307370 q = 1) (hb : d312064 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307370, d312064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307370, d312064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307498 q = 1) (hb : d312190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307498, d312190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307498, d312190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307499 q = 1) (hb : d312191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307499, d312191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307499, d312191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307500 q = 1) (hb : d312192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307500, d312192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307500, d312192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307501 q = 1) (hb : d312193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307501, d312193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307501, d312193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81537 q ha hb
  have h15 (q : Pattern) (ha : d307377 q = 1) (hb : d312069 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307377, d312069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81537 q ha hb
    | true =>
      simp only [d307377, d312069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307502 q = 1) (hb : d312194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307502, d312194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307502, d312194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307378 q = 1) (hb : d312070 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307378, d312070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307378, d312070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307503 q = 1) (hb : d312195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307503, d312195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307503, d312195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307504 q = 1) (hb : d312196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307504, d312196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307504, d312196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307505 q = 1) (hb : d312197 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307505, d312197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307505, d312197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
  have h21 (q : Pattern) (ha : d307262 q = 1) (hb : d311959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
    | true =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307506 q = 1) (hb : d312198 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307506, d312198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307506, d312198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d307263 q = 1) (hb : d311960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d307507 q = 1) (hb : d312199 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307507, d312199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d307507, d312199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d307508 q = 1) (hb : d312200 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307508, d312200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d307508, d312200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d307509 q = 1) (hb : d312201 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307509, d312201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307509, d312201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d307510 q = 1) (hb : d312202 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307510, d312202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307510, d312202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro81562 (p : Pattern) (ha : d307525 p = 1) (hb : d312217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307511 q = 1) (hb : d312203 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307511, d312203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307511, d312203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81511 q ha hb
  have h2 (q : Pattern) (ha : d307233 q = 1) (hb : d311937 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307233, d311937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81511 q ha hb
    | true =>
      simp only [d307233, d311937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307512 q = 1) (hb : d312204 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307512, d312204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307512, d312204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307234 q = 1) (hb : d311938 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307234, d311938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307234, d311938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307513 q = 1) (hb : d312205 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307513, d312205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307513, d312205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307514 q = 1) (hb : d312206 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307514, d312206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307514, d312206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307515 q = 1) (hb : d312207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307515, d312207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307515, d312207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81514 q ha hb
  have h8 (q : Pattern) (ha : d307251 q = 1) (hb : d311950 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307251, d311950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81514 q ha hb
    | true =>
      simp only [d307251, d311950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307516 q = 1) (hb : d312208 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307516, d312208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307516, d312208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307252 q = 1) (hb : d311951 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307252, d311951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307252, d311951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307517 q = 1) (hb : d312209 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307517, d312209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307517, d312209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307518 q = 1) (hb : d312210 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307518, d312210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307518, d312210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307519 q = 1) (hb : d312211 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307519, d312211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307519, d312211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307505 q = 1) (hb : d312197 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307505, d312197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307505, d312197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
  have h15 (q : Pattern) (ha : d307262 q = 1) (hb : d311959 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81515 q ha hb
    | true =>
      simp only [d307262, d311959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307506 q = 1) (hb : d312198 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307506, d312198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307506, d312198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307263 q = 1) (hb : d311960 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307263, d311960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307507 q = 1) (hb : d312199 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307507, d312199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307507, d312199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307508 q = 1) (hb : d312200 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307508, d312200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307508, d312200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307520 q = 1) (hb : d312212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
  have h21 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307521 q = 1) (hb : d312213 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d307522 q = 1) (hb : d312214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d307523 q = 1) (hb : d312215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d307524 q = 1) (hb : d312216 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307524, d312216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307524, d312216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d307525 q = 1) (hb : d312217 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307525, d312217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307525, d312217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro81563 (p : Pattern) (ha : d307535 p = 1) (hb : d312227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307529 q = 1) (hb : d312221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307529, d312221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307529, d312221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81539 q ha hb
  have h2 (q : Pattern) (ha : d307392 q = 1) (hb : d312084 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307392, d312084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81539 q ha hb
    | true =>
      simp only [d307392, d312084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307530 q = 1) (hb : d312222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307530, d312222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307530, d312222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307393 q = 1) (hb : d312085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307393, d312085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307393, d312085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307531 q = 1) (hb : d312223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307531, d312223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307531, d312223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307532 q = 1) (hb : d312224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307532, d312224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307532, d312224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307520 q = 1) (hb : d312212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
  have h8 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307521 q = 1) (hb : d312213 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307522 q = 1) (hb : d312214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307523 q = 1) (hb : d312215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307533 q = 1) (hb : d312225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307533, d312225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307533, d312225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307534 q = 1) (hb : d312226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307534, d312226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307534, d312226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307535 q = 1) (hb : d312227 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307535, d312227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307535, d312227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81564 (p : Pattern) (ha : d307549 p = 1) (hb : d312241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307540 q = 1) (hb : d312232 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307540, d312232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307540, d312232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
  have h2 (q : Pattern) (ha : d307286 q = 1) (hb : d311983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
    | true =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307541 q = 1) (hb : d312233 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307541, d312233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307541, d312233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307287 q = 1) (hb : d311984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307542 q = 1) (hb : d312234 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307542, d312234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307542, d312234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307543 q = 1) (hb : d312235 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307543, d312235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307543, d312235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307544 q = 1) (hb : d312236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
  have h8 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307545 q = 1) (hb : d312237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307546 q = 1) (hb : d312238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307547 q = 1) (hb : d312239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307548 q = 1) (hb : d312240 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307548, d312240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307548, d312240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307520 q = 1) (hb : d312212 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307520, d312212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
  have h15 (q : Pattern) (ha : d307273 q = 1) (hb : d311970 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81517 q ha hb
    | true =>
      simp only [d307273, d311970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307521 q = 1) (hb : d312213 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307521, d312213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307274 q = 1) (hb : d311971 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307274, d311971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307522 q = 1) (hb : d312214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307522, d312214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307523 q = 1) (hb : d312215 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307523, d312215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307534 q = 1) (hb : d312226 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307534, d312226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307534, d312226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307549 q = 1) (hb : d312241 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307549, d312241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307549, d312241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro81565 (p : Pattern) (ha : d307554 p = 1) (hb : d312246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307544 q = 1) (hb : d312236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
  have h2 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307545 q = 1) (hb : d312237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307546 q = 1) (hb : d312238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307547 q = 1) (hb : d312239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307553 q = 1) (hb : d312245 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307553, d312245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307553, d312245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d307554 q = 1) (hb : d312246 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307554, d312246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307554, d312246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro81566 (p : Pattern) (ha : d307560 p = 1) (hb : d312252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307526 q = 1) (hb : d312218 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307526, d312218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81561 q ha hb
    | true =>
      simp only [d307526, d312218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81562 q ha hb
  have h2 (q : Pattern) (ha : d307527 q = 1) (hb : d312219 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307527, d312219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307527, d312219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307528 q = 1) (hb : d312220 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307528, d312220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307528, d312220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307536 q = 1) (hb : d312228 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307536, d312228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81562 q ha hb
    | true =>
      simp only [d307536, d312228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81563 q ha hb
  have h5 (q : Pattern) (ha : d307537 q = 1) (hb : d312229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307537, d312229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307537, d312229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307538 q = 1) (hb : d312230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307538, d312230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307538, d312230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307539 q = 1) (hb : d312231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307539, d312231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307539, d312231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307550 q = 1) (hb : d312242 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81562 q ha hb
    | true =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
  have h9 (q : Pattern) (ha : d307551 q = 1) (hb : d312243 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307552 q = 1) (hb : d312244 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307555 q = 1) (hb : d312247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
    | true =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81565 q ha hb
  have h12 (q : Pattern) (ha : d307556 q = 1) (hb : d312248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307557 q = 1) (hb : d312249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307558 q = 1) (hb : d312250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307559 q = 1) (hb : d312251 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307559, d312251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307559, d312251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307560 q = 1) (hb : d312252 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307560, d312252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307560, d312252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro81567 (p : Pattern) (ha : d307565 p = 1) (hb : d312257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307550 q = 1) (hb : d312242 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81562 q ha hb
    | true =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
  have h2 (q : Pattern) (ha : d307551 q = 1) (hb : d312243 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307552 q = 1) (hb : d312244 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307555 q = 1) (hb : d312247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
    | true =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81565 q ha hb
  have h5 (q : Pattern) (ha : d307556 q = 1) (hb : d312248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307557 q = 1) (hb : d312249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307558 q = 1) (hb : d312250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307563 q = 1) (hb : d312255 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307563, d312255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307563, d312255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307564 q = 1) (hb : d312256 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307564, d312256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307564, d312256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307565 q = 1) (hb : d312257 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307565, d312257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307565, d312257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro81568 (p : Pattern) (ha : d307571 p = 1) (hb : d312263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307561 q = 1) (hb : d312253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307561, d312253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81566 q ha hb
    | true =>
      simp only [d307561, d312253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307562 q = 1) (hb : d312254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307562, d312254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307562, d312254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307566 q = 1) (hb : d312258 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307566, d312258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81567 q ha hb
    | true =>
      simp only [d307566, d312258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307567 q = 1) (hb : d312259 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307567, d312259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307567, d312259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307568 q = 1) (hb : d312260 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307568, d312260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307568, d312260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307569 q = 1) (hb : d312261 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307569, d312261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307569, d312261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307570 q = 1) (hb : d312262 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307570, d312262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307570, d312262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307571 q = 1) (hb : d312263 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307571, d312263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307571, d312263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81569 (p : Pattern) (ha : d307573 p = 1) (hb : d312265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307555 q = 1) (hb : d312247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
    | true =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81565 q ha hb
  have h2 (q : Pattern) (ha : d307556 q = 1) (hb : d312248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307557 q = 1) (hb : d312249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307563 q = 1) (hb : d312255 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307563, d312255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307563, d312255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307572 q = 1) (hb : d312264 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307572, d312264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307572, d312264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307573 q = 1) (hb : d312265 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307573, d312265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307573, d312265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81570 (p : Pattern) (ha : d307579 p = 1) (hb : d312271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307566 q = 1) (hb : d312258 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307566, d312258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81567 q ha hb
    | true =>
      simp only [d307566, d312258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307567 q = 1) (hb : d312259 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307567, d312259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307567, d312259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307574 q = 1) (hb : d312266 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307574, d312266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81569 q ha hb
    | true =>
      simp only [d307574, d312266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307575 q = 1) (hb : d312267 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307575, d312267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307575, d312267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307576 q = 1) (hb : d312268 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307576, d312268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307576, d312268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307577 q = 1) (hb : d312269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307577, d312269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307577, d312269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307578 q = 1) (hb : d312270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307578, d312270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307578, d312270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307579 q = 1) (hb : d312271 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307579, d312271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307579, d312271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81571 (p : Pattern) (ha : d307592 p = 1) (hb : d312279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307540 q = 1) (hb : d312232 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307540, d312232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307540, d312232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
  have h2 (q : Pattern) (ha : d307286 q = 1) (hb : d311983 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81519 q ha hb
    | true =>
      simp only [d307286, d311983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307541 q = 1) (hb : d312233 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307541, d312233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307541, d312233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307287 q = 1) (hb : d311984 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307287, d311984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307542 q = 1) (hb : d312234 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307542, d312234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307542, d312234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307543 q = 1) (hb : d312235 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307543, d312235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307543, d312235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307544 q = 1) (hb : d312236 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307544, d312236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
  have h8 (q : Pattern) (ha : d307291 q = 1) (hb : d311988 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81520 q ha hb
    | true =>
      simp only [d307291, d311988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307545 q = 1) (hb : d312237 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307545, d312237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307292 q = 1) (hb : d311989 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307292, d311989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307546 q = 1) (hb : d312238 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307546, d312238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307547 q = 1) (hb : d312239 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307547, d312239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307548 q = 1) (hb : d312240 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307548, d312240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307548, d312240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307587 q = 1) (hb : d312274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307587, d312274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307587, d312274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81543 q ha hb
  have h15 (q : Pattern) (ha : d307413 q = 1) (hb : d312105 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307413, d312105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81543 q ha hb
    | true =>
      simp only [d307413, d312105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307588 q = 1) (hb : d312275 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307588, d312275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307588, d312275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307414 q = 1) (hb : d312106 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307414, d312106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307414, d312106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307589 q = 1) (hb : d312276 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307589, d312276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307589, d312276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307590 q = 1) (hb : d312277 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307590, d312277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307590, d312277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307591 q = 1) (hb : d312278 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307591, d312278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307591, d312278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307592 q = 1) (hb : d312279 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307592, d312279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307592, d312279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro81572 (p : Pattern) (ha : d307598 p = 1) (hb : d312285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307593 q = 1) (hb : d312280 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307593, d312280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307593, d312280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81545 q ha hb
  have h2 (q : Pattern) (ha : d307420 q = 1) (hb : d312112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307420, d312112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81545 q ha hb
    | true =>
      simp only [d307420, d312112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307594 q = 1) (hb : d312281 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307594, d312281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307594, d312281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307421 q = 1) (hb : d312113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307421, d312113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307421, d312113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307595 q = 1) (hb : d312282 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307595, d312282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307595, d312282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307596 q = 1) (hb : d312283 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307596, d312283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307596, d312283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307597 q = 1) (hb : d312284 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307597, d312284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307597, d312284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307598 q = 1) (hb : d312285 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307598, d312285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307598, d312285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81573 (p : Pattern) (ha : d307604 p = 1) (hb : d312291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307550 q = 1) (hb : d312242 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81562 q ha hb
    | true =>
      simp only [d307550, d312242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
  have h2 (q : Pattern) (ha : d307551 q = 1) (hb : d312243 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307551, d312243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307552 q = 1) (hb : d312244 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307552, d312244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307555 q = 1) (hb : d312247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81564 q ha hb
    | true =>
      simp only [d307555, d312247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81565 q ha hb
  have h5 (q : Pattern) (ha : d307556 q = 1) (hb : d312248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d312248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307557 q = 1) (hb : d312249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d312249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307558 q = 1) (hb : d312250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307558, d312250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307599 q = 1) (hb : d312286 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307599, d312286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81571 q ha hb
    | true =>
      simp only [d307599, d312286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81572 q ha hb
  have h9 (q : Pattern) (ha : d307600 q = 1) (hb : d312287 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307600, d312287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307600, d312287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307601 q = 1) (hb : d312288 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307601, d312288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307601, d312288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307602 q = 1) (hb : d312289 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307602, d312289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307602, d312289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307603 q = 1) (hb : d312290 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307603, d312290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307603, d312290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307604 q = 1) (hb : d312291 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307604, d312291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307604, d312291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro81574 (p : Pattern) (ha : d307610 p = 1) (hb : d312297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307605 q = 1) (hb : d312292 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307605, d312292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81573 q ha hb
    | true =>
      simp only [d307605, d312292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307606 q = 1) (hb : d312293 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307606, d312293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307606, d312293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307607 q = 1) (hb : d312294 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307607, d312294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307607, d312294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307608 q = 1) (hb : d312295 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307608, d312295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307608, d312295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307609 q = 1) (hb : d312296 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307609, d312296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307609, d312296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307610 q = 1) (hb : d312297 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307610, d312297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307610, d312297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81575 (p : Pattern) (ha : d307616 p = 1) (hb : d312303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307580 q = 1) (hb : d312272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307580, d312272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81568 q ha hb
    | true =>
      simp only [d307580, d312272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81570 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d312273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d312273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307586, d312273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307611 q = 1) (hb : d312298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307611, d312298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81574 q ha hb
    | true =>
      simp only [d307611, d312298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307612 q = 1) (hb : d312299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307612, d312299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307612, d312299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307613 q = 1) (hb : d312300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d312300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d312300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307614 q = 1) (hb : d312301 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d312301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d312301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307615 q = 1) (hb : d312302 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d312302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d312302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307616 q = 1) (hb : d312303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d312303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d312303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81576 (p : Pattern) (ha : d307584 p = 1) (hb : d312308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307574 q = 1) (hb : d312266 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307574, d312266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81569 q ha hb
    | true =>
      simp only [d307574, d312266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307575 q = 1) (hb : d312267 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307575, d312267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307575, d312267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307581 q = 1) (hb : d312305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307581, d312305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307581, d312305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307582 q = 1) (hb : d312306 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307582, d312306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307582, d312306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307583 q = 1) (hb : d312307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307583, d312307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307583, d312307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307584 q = 1) (hb : d312308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307584, d312308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307584, d312308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81577 (p : Pattern) (ha : d307623 p = 1) (hb : d312314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307618 q = 1) (hb : d312309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307618, d312309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81576 q ha hb
    | true =>
      simp only [d307618, d312309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307619 q = 1) (hb : d312310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307619, d312310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307619, d312310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307620 q = 1) (hb : d312311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307620, d312311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307620, d312311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307621 q = 1) (hb : d312312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307621, d312312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307621, d312312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307622 q = 1) (hb : d312313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307622, d312313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307622, d312313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307623 q = 1) (hb : d312314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307623, d312314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307623, d312314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81578 (p : Pattern) (ha : d307629 p = 1) (hb : d312320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307330 q = 1) (hb : d312027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307330, d312027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307330, d312027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81527 q ha hb
  have h2 (q : Pattern) (ha : d307331 q = 1) (hb : d312028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307331, d312028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307331, d312028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307340 q = 1) (hb : d312037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307340, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81527 q ha hb
    | true =>
      simp only [d307340, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81530 q ha hb
  have h4 (q : Pattern) (ha : d307341 q = 1) (hb : d312038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307341, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307341, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307342 q = 1) (hb : d312039 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307342, d312039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307342, d312039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307465 q = 1) (hb : d312157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d312157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81549 q ha hb
    | true =>
      simp only [d307465, d312157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81556 q ha hb
  have h7 (q : Pattern) (ha : d307478 q = 1) (hb : d312170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307478, d312170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81557 q ha hb
    | true =>
      simp only [d307478, d312170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81558 q ha hb
  have h8 (q : Pattern) (ha : d307479 q = 1) (hb : d312171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d312171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307479, d312171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307480 q = 1) (hb : d312172 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d312172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307480, d312172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307481 q = 1) (hb : d312173 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d312173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307481, d312173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307485 q = 1) (hb : d312177 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d312177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307485, d312177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81559 q ha hb
  have h12 (q : Pattern) (ha : d307487 q = 1) (hb : d312179 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307487, d312179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307487, d312179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81560 q ha hb
  have h13 (q : Pattern) (ha : d307488 q = 1) (hb : d312180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d312180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307488, d312180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307489 q = 1) (hb : d312181 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d312181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307489, d312181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307490 q = 1) (hb : d312182 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d312182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307490, d312182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307491 q = 1) (hb : d312183 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d312183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307491, d312183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307617 q = 1) (hb : d312304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d312304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307617, d312304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81575 q ha hb
  have h18 (q : Pattern) (ha : d307624 q = 1) (hb : d312315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307624, d312315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307624, d312315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81577 q ha hb
  have h19 (q : Pattern) (ha : d307625 q = 1) (hb : d312316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d312316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307625, d312316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307626 q = 1) (hb : d312317 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d312317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307626, d312317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307627 q = 1) (hb : d312318 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d312318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307627, d312318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307628 q = 1) (hb : d312319 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d312319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307628, d312319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307629 q = 1) (hb : d312320 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d312320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307629, d312320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro81579 (p : Pattern) (ha : d307635 p = 1) (hb : d312326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d312321 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d312321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d312321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81578 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d312322 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d312322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d312322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d312323 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d312323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d312323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d312324 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d312324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d312324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d312325 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d312325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d312325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d312326 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d312326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d312326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81580 (p : Pattern) (ha : d307931 p = 1) (hb : d312332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d311254 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d311254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81342 q ha hb
    | true =>
      simp only [d306523, d311254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81389 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d311535 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d311535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d311535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81444 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d311536 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d311536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d311536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d311922 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d311922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d311922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81508 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d311923 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d311923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d311923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d311924 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d311924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d311924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d312327 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d312327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d312327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81579 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d312328 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d312328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d312328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d312329 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d312329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d312329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d312330 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d312330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d312330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d309506 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d309506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d309506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80435 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d309507 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d309507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d309507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d309508 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d309508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d309508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d309509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d309509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d312331 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d312331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d312331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d312332 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d312332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d312332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro81581 (p : Pattern) (ha : d307937 p = 1) (hb : d312338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d312333 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d312333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81580 q ha hb
    | true =>
      simp only [d307932, d312333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d312334 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d312334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d312334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d312335 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d312335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d312335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d312336 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d312336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d312336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d312337 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d312337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d312337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d312338 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d312338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d312338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81582 (p : Pattern) (ha : d307943 p = 1) (hb : d312344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d312339 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d312339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81581 q ha hb
    | true =>
      simp only [d307938, d312339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d312340 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d312340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d312340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d312341 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d312341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d312341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d312342 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d312342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d312342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d312343 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d312343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d312343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d312344 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d312344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d312344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81583 (p : Pattern) (ha : d307949 p = 1) (hb : d312350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d312345 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d312345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81582 q ha hb
    | true =>
      simp only [d307944, d312345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d312346 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d312346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d312346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d312347 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d312347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d312347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d312348 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d312348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d312348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d312349 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d312349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d312349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d312350 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d312350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d312350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81584 (p : Pattern) (ha : d307955 p = 1) (hb : d312356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d312351 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d312351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81583 q ha hb
    | true =>
      simp only [d307950, d312351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d312352 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d312352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d312352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d312353 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d312353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d312353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d312354 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d312354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d312354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d312355 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d312355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d312355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d312356 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d312356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d312356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81585 (p : Pattern) (ha : d307961 p = 1) (hb : d312362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d312357 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d312357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81584 q ha hb
    | true =>
      simp only [d307956, d312357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d312358 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d312358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d312358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d312359 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d312359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d312359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d312360 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d312360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d312360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d312361 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d312361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d312361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d312362 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d312362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d312362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81586 (p : Pattern) (ha : d307967 p = 1) (hb : d312368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d312363 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d312363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81585 q ha hb
    | true =>
      simp only [d307962, d312363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d312364 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d312364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d312364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d312365 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d312365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d312365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d312366 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d312366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d312366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d312367 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d312367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d312367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d312368 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d312368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d312368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81587 (p : Pattern) (ha : d307973 p = 1) (hb : d312374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d312369 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d312369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81586 q ha hb
    | true =>
      simp only [d307968, d312369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d312370 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d312370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d312370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d312371 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d312371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d312371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d312372 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d312372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d312372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d312373 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d312373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d312373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d312374 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d312374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d312374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81588 (p : Pattern) (ha : d310774 p = 1) (hb : d312377 p = 1) : d312622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d310774 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d310774 q = 1) : d310808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80952 q ha hb
    | true =>
      simp only [d33246, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33306 q = 1) (hb : d310774 q = 1) : d310868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33307 q = 1) (hb : d310774 q = 1) : d310869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33307, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33308 q = 1) (hb : d310774 q = 1) : d310870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33309 q = 1) (hb : d310774 q = 1) : d310871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312377 q = 1) : d312622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312377, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312377, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro81589 (p : Pattern) (ha : d310774 p = 1) (hb : d312387 p = 1) : d312632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d310774 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33282 q = 1) (hb : d310774 q = 1) : d310844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80957 q ha hb
    | true =>
      simp only [d33282, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312383 q = 1) : d312628 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312383, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312383, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312384 q = 1) : d312629 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312384, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312384, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312385 q = 1) : d312630 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312385, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312385, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312386 q = 1) : d312631 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312386, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312386, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312387 q = 1) : d312632 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312387, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312387, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81590 (p : Pattern) (ha : d310774 p = 1) (hb : d312393 p = 1) : d312638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33311 q = 1) (hb : d310774 q = 1) : d310873 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80960 q ha hb
    | true =>
      simp only [d33311, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80961 q ha hb
  have h2 (q : Pattern) (ha : d33312 q = 1) (hb : d310774 q = 1) : d310874 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33312, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312375 q = 1) : d312620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312375, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312375, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312376 q = 1) : d312621 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312376, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312376, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312378 q = 1) : d312623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312378, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312378, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81588 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312379 q = 1) : d312624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312379, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312379, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312380 q = 1) : d312625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312380, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312380, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312381 q = 1) : d312626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312381, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312381, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312382 q = 1) : d312627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312382, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312382, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312388 q = 1) : d312633 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312388, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312388, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81589 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312389 q = 1) : d312634 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312389, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312389, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312390 q = 1) : d312635 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312390, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312390, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312391 q = 1) : d312636 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312391, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312391, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312392 q = 1) : d312637 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312392, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312392, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312393 q = 1) : d312638 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312393, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312393, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81591 (p : Pattern) (ha : d310774 p = 1) (hb : d312399 p = 1) : d312644 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d310774 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312394 q = 1) : d312639 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312394, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312394, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81590 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312395 q = 1) : d312640 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312395, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312395, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312396 q = 1) : d312641 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312396, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312396, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312397 q = 1) : d312642 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312397, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312397, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312398 q = 1) : d312643 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312398, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312398, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312399 q = 1) : d312644 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312399, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312399, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81592 (p : Pattern) (ha : d310774 p = 1) (hb : d312402 p = 1) : d312647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33527 q = 1) (hb : d310774 q = 1) : d311041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80991 q ha hb
    | true =>
      simp only [d33527, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80992 q ha hb
  have h2 (q : Pattern) (ha : d33528 q = 1) (hb : d310774 q = 1) : d311042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33529 q = 1) (hb : d310774 q = 1) : d311043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33529, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33530 q = 1) (hb : d310774 q = 1) : d311044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33531 q = 1) (hb : d310774 q = 1) : d311045 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312402 q = 1) : d312647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312402, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312402, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro81593 (p : Pattern) (ha : d310774 p = 1) (hb : d312413 p = 1) : d312658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312408 q = 1) : d312653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312408, d312653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81028 q hb ha
    | true =>
      simp only [d312408, d312653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80998 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312409 q = 1) : d312654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312409, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312409, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312410 q = 1) : d312655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312410, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312410, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312411 q = 1) : d312656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312411, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312411, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312412 q = 1) : d312657 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312412, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312412, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312413 q = 1) : d312658 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312413, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312413, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81594 (p : Pattern) (ha : d310774 p = 1) (hb : d312419 p = 1) : d312664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33533 q = 1) (hb : d310774 q = 1) : d311047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33533, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80990 q ha hb
    | true =>
      simp only [d33533, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80993 q ha hb
  have h2 (q : Pattern) (ha : d33534 q = 1) (hb : d310774 q = 1) : d311048 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33534, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33534, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312400 q = 1) : d312645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312400, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312400, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312401 q = 1) : d312646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312401, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312401, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312403 q = 1) : d312648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312403, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312403, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81592 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312404 q = 1) : d312649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312404, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312404, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312405 q = 1) : d312650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312405, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312405, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312406 q = 1) : d312651 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312406, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312406, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312407 q = 1) : d312652 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312407, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312407, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312414 q = 1) : d312659 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312414, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312414, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81593 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312415 q = 1) : d312660 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312415, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312415, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312416 q = 1) : d312661 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312416, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312416, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312417 q = 1) : d312662 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312417, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312417, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312418 q = 1) : d312663 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312418, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312418, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312419 q = 1) : d312664 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312419, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312419, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81595 (p : Pattern) (ha : d310774 p = 1) (hb : d312425 p = 1) : d312670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312420 q = 1) : d312665 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312420, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312420, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81594 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312421 q = 1) : d312666 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312421, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312421, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312422 q = 1) : d312667 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312422, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312422, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312423 q = 1) : d312668 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312423, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312423, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312424 q = 1) : d312669 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312424, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312424, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312425 q = 1) : d312670 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312425, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312425, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81596 (p : Pattern) (ha : d310774 p = 1) (hb : d312429 p = 1) : d312674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33867 q = 1) (hb : d310774 q = 1) : d311300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33867, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81042 q ha hb
    | true =>
      simp only [d33867, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81043 q ha hb
  have h2 (q : Pattern) (ha : d33868 q = 1) (hb : d310774 q = 1) : d311301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33868, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33868, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33869 q = 1) (hb : d310774 q = 1) : d311302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33869, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33869, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33870 q = 1) (hb : d310774 q = 1) : d311303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33870, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33870, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33871 q = 1) (hb : d310774 q = 1) : d311304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33871, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33871, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312429 q = 1) : d312674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312429, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312429, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro81597 (p : Pattern) (ha : d310774 p = 1) (hb : d312440 p = 1) : d312685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312435 q = 1) : d312680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312435, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81083 q hb ha
    | true =>
      simp only [d312435, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81051 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312436 q = 1) : d312681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312436, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312436, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312437 q = 1) : d312682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312437, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312437, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312438 q = 1) : d312683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312438, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312438, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312439 q = 1) : d312684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312439, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312439, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312440 q = 1) : d312685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312440, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312440, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81598 (p : Pattern) (ha : d310774 p = 1) (hb : d312446 p = 1) : d312691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33873 q = 1) (hb : d310774 q = 1) : d311306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33873, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81041 q ha hb
    | true =>
      simp only [d33873, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81044 q ha hb
  have h2 (q : Pattern) (ha : d33874 q = 1) (hb : d310774 q = 1) : d311307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33874, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33874, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312427 q = 1) : d312672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312427, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312427, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312428 q = 1) : d312673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312428, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312428, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312430 q = 1) : d312675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312430, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312430, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81596 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312431 q = 1) : d312676 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312431, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312431, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312432 q = 1) : d312677 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312432, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312432, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312433 q = 1) : d312678 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312433, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312433, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312434 q = 1) : d312679 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312434, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312434, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312441 q = 1) : d312686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312441, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312441, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81597 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312442 q = 1) : d312687 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312442, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312442, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312443 q = 1) : d312688 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312443, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312443, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312444 q = 1) : d312689 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312444, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312444, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312445 q = 1) : d312690 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312445, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312445, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312446 q = 1) : d312691 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312446, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312446, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81599 (p : Pattern) (ha : d310774 p = 1) (hb : d312452 p = 1) : d312697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312447 q = 1) : d312692 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312447, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312447, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81598 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312448 q = 1) : d312693 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312448, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312448, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312449 q = 1) : d312694 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312449, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312449, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312450 q = 1) : d312695 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312450, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312450, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312451 q = 1) : d312696 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312451, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312451, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312452 q = 1) : d312697 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312452, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312452, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81600 (p : Pattern) (ha : d310774 p = 1) (hb : d312457 p = 1) : d312702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34326 q = 1) (hb : d310774 q = 1) : d311638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34326, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81102 q ha hb
    | true =>
      simp only [d34326, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81103 q ha hb
  have h2 (q : Pattern) (ha : d34327 q = 1) (hb : d310774 q = 1) : d311639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34327, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34327, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34328 q = 1) (hb : d310774 q = 1) : d311640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34328, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34328, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34329 q = 1) (hb : d310774 q = 1) : d311641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34329, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34329, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34330 q = 1) (hb : d310774 q = 1) : d311642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34330, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34330, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312457 q = 1) : d312702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312457, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312457, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro81601 (p : Pattern) (ha : d310774 p = 1) (hb : d312468 p = 1) : d312713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312463 q = 1) : d312708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312463, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81145 q hb ha
    | true =>
      simp only [d312463, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81111 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312464 q = 1) : d312709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312464, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312464, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312465 q = 1) : d312710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312465, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312465, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312466 q = 1) : d312711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312466, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312466, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312467 q = 1) : d312712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312467, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312467, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312468 q = 1) : d312713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312468, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312468, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81602 (p : Pattern) (ha : d310774 p = 1) (hb : d312474 p = 1) : d312719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34332 q = 1) (hb : d310774 q = 1) : d311644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34332, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81101 q ha hb
    | true =>
      simp only [d34332, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81104 q ha hb
  have h2 (q : Pattern) (ha : d34333 q = 1) (hb : d310774 q = 1) : d311645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34333, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34333, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312455 q = 1) : d312700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312455, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312455, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312456 q = 1) : d312701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312456, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312456, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312458 q = 1) : d312703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312458, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312458, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81600 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312459 q = 1) : d312704 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312459, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312459, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312460 q = 1) : d312705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312460, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312460, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312461 q = 1) : d312706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312461, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312461, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312462 q = 1) : d312707 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312462, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312462, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312469 q = 1) : d312714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312469, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312469, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81601 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312470 q = 1) : d312715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312470, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312470, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312471 q = 1) : d312716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312471, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312471, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312472 q = 1) : d312717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312472, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312472, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312473 q = 1) : d312718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312473, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312473, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312474 q = 1) : d312719 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312474, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312474, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81603 (p : Pattern) (ha : d310774 p = 1) (hb : d312480 p = 1) : d312725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312475 q = 1) : d312720 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312475, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312475, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81602 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312476 q = 1) : d312721 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312476, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312476, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312477 q = 1) : d312722 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312477, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312477, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312478 q = 1) : d312723 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312478, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312478, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312479 q = 1) : d312724 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312479, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312479, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312480 q = 1) : d312725 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312480, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312480, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81604 (p : Pattern) (ha : d310774 p = 1) (hb : d312486 p = 1) : d312731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34892 q = 1) (hb : d310774 q = 1) : d312031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34892, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81167 q ha hb
    | true =>
      simp only [d34892, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81168 q ha hb
  have h2 (q : Pattern) (ha : d34893 q = 1) (hb : d310774 q = 1) : d312032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34893, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34893, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34894 q = 1) (hb : d310774 q = 1) : d312033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34894, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34894, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34895 q = 1) (hb : d310774 q = 1) : d312034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34895, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34895, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34896 q = 1) (hb : d310774 q = 1) : d312035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34896, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34896, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312486 q = 1) : d312731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312486, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312486, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro81605 (p : Pattern) (ha : d310774 p = 1) (hb : d312497 p = 1) : d312742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312492 q = 1) : d312737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312492, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81211 q hb ha
    | true =>
      simp only [d312492, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81176 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312493 q = 1) : d312738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312493, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312493, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312494 q = 1) : d312739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312494, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312494, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312495 q = 1) : d312740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312495, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312495, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312496 q = 1) : d312741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312496, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312496, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312497 q = 1) : d312742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312497, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312497, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81606 (p : Pattern) (ha : d310774 p = 1) (hb : d312503 p = 1) : d312748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34898 q = 1) (hb : d310774 q = 1) : d312037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34898, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81166 q ha hb
    | true =>
      simp only [d34898, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81169 q ha hb
  have h2 (q : Pattern) (ha : d34899 q = 1) (hb : d310774 q = 1) : d312038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34899, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34899, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312484 q = 1) : d312729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312484, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312484, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312485 q = 1) : d312730 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312485, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312485, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312487 q = 1) : d312732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312487, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312487, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81604 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312488 q = 1) : d312733 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312488, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312488, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312489 q = 1) : d312734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312489, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312489, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312490 q = 1) : d312735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312490, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312490, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312491 q = 1) : d312736 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312491, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312491, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312498 q = 1) : d312743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312498, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312498, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81605 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312499 q = 1) : d312744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312499, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312499, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312500 q = 1) : d312745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312500, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312500, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312501 q = 1) : d312746 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312501, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312501, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312502 q = 1) : d312747 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312502, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312502, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312503 q = 1) : d312748 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312503, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312503, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81607 (p : Pattern) (ha : d310774 p = 1) (hb : d312509 p = 1) : d312754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312504 q = 1) : d312749 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312504, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312504, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81606 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312505 q = 1) : d312750 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312505, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312505, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312506 q = 1) : d312751 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312506, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312506, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312507 q = 1) : d312752 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312507, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312507, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312508 q = 1) : d312753 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312508, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312508, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312509 q = 1) : d312754 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312509, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312509, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81608 (p : Pattern) (ha : d310774 p = 1) (hb : d312516 p = 1) : d309695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35475 q = 1) (hb : d310774 q = 1) : d44509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d35475, d44509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81243 q ha hb
    | true =>
      simp only [d35475, d44509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81244 q ha hb
  have h2 (q : Pattern) (ha : d35476 q = 1) (hb : d310774 q = 1) : d44510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d35476, d44510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35476, d44510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35477 q = 1) (hb : d310774 q = 1) : d44511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d35477, d44511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35477, d44511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35478 q = 1) (hb : d310774 q = 1) : d44512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d35478, d44512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35478, d44512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35479 q = 1) (hb : d310774 q = 1) : d44513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d35479, d44513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35479, d44513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312516 q = 1) : d309695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312516, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312516, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro81609 (p : Pattern) (ha : d310774 p = 1) (hb : d312523 p = 1) : d44723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35771 q = 1) (hb : d310774 q = 1) : d44703 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35771, d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81281 q ha hb
    | true =>
      simp only [d35771, d44703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81251 q ha hb
  have h2 (q : Pattern) (ha : d35772 q = 1) (hb : d310774 q = 1) : d44704 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35772, d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35772, d44704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35773 q = 1) (hb : d310774 q = 1) : d44705 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35773, d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35773, d44705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35780 q = 1) (hb : d310774 q = 1) : d44713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35780, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81251 q ha hb
    | true =>
      simp only [d35780, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81283 q ha hb
  have h5 (q : Pattern) (ha : d35781 q = 1) (hb : d310774 q = 1) : d44714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35781, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35781, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35782 q = 1) (hb : d310774 q = 1) : d44715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35782, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35782, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d35783 q = 1) (hb : d310774 q = 1) : d44716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35783, d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35783, d44716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d35799 q = 1) (hb : d310774 q = 1) : d44713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35799, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81251 q ha hb
    | true =>
      simp only [d35799, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81252 q ha hb
  have h9 (q : Pattern) (ha : d35800 q = 1) (hb : d310774 q = 1) : d44714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35800, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35800, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d35801 q = 1) (hb : d310774 q = 1) : d44715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35801, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35801, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d35802 q = 1) (hb : d310774 q = 1) : d44721 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35802, d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d35802, d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312522 q = 1) : d44722 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312522, d44722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312522, d44722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312523 q = 1) : d44723 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312523, d44723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312523, d44723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro81610 (p : Pattern) (ha : d310774 p = 1) (hb : d312529 p = 1) : d44737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312524 q = 1) : d44724 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312524, d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81609 q ha hb
    | true =>
      simp only [d312524, d44724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312525 q = 1) : d44725 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312525, d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312525, d44725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35805 q = 1) (hb : d310774 q = 1) : d44732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d35805, d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81253 q ha hb
    | true =>
      simp only [d35805, d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35806 q = 1) (hb : d310774 q = 1) : d44733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d35806, d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35806, d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312526 q = 1) : d44734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312526, d44734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312526, d44734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312527 q = 1) : d44735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312527, d44735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312527, d44735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312528 q = 1) : d44736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312528, d44736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312528, d44736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312529 q = 1) : d44737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312529, d44737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312529, d44737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro81611 (p : Pattern) (ha : d258695 p = 1) (hb : d310774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44880 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44880, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46865 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d46866 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d310774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46866, d310774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d258695 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81612 (p : Pattern) (ha : d310774 p = 1) (hb : d312535 p = 1) : d44471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d310774 q = 1) : d44451 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d44451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81224 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312530 q = 1) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d312530, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81611 q hb ha
    | true =>
      simp only [d312530, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81225 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312531 q = 1) : d44452 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d312531, d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312531, d44452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312532 q = 1) : d44453 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d312532, d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312532, d44453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d10405 q = 1) (hb : d310774 q = 1) : d44454 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81224 q ha hb
    | true =>
      simp only [d10405, d44454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10406 q = 1) (hb : d310774 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81225 q ha hb
    | true =>
      simp only [d10406, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10407 q = 1) (hb : d310774 q = 1) : d44455 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10407, d44455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10408 q = 1) (hb : d310774 q = 1) : d44456 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10408, d44456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312533 q = 1) : d44457 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d312533, d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312533, d44457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312534 q = 1) : d44458 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d312534, d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312534, d44458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312535 q = 1) : d44471 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d312535, d44471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312535, d44471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro81613 (p : Pattern) (ha : d310774 p = 1) (hb : d312541 p = 1) : d44712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35765 q = 1) (hb : d310774 q = 1) : d44692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35765, d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35765, d44692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81232 q ha hb
  have h2 (q : Pattern) (ha : d35417 q = 1) (hb : d310774 q = 1) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35417, d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81232 q ha hb
    | true =>
      simp only [d35417, d44460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35766 q = 1) (hb : d310774 q = 1) : d44693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35766, d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35766, d44693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35418 q = 1) (hb : d310774 q = 1) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35418, d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35418, d44461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35767 q = 1) (hb : d310774 q = 1) : d44694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35767, d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35767, d44694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35768 q = 1) (hb : d310774 q = 1) : d44695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35768, d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35768, d44695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35797 q = 1) (hb : d310774 q = 1) : d44701 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d35797, d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35797, d44701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d310774 q = 1) : d44707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d44707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d44707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81234 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d310774 q = 1) : d44472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81234 q ha hb
    | true =>
      simp only [d10412, d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d310774 q = 1) : d44708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d44708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d44708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312536 q = 1) : d44472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d312536, d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81612 q ha hb
    | true =>
      simp only [d312536, d44472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312537 q = 1) : d44473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d312537, d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312537, d44473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312538 q = 1) : d44709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d312538, d44709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d312538, d44709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312539 q = 1) : d44710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d312539, d44710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312539, d44710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312540 q = 1) : d44711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d312540, d44711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d312540, d44711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d310774 q = 1) (hb : d312541 q = 1) : d44712 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d312541, d44712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312541, d44712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro81614 (p : Pattern) (ha : d310774 p = 1) (hb : d312547 p = 1) : d44731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312542 q = 1) : d44713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d312542, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81251 q hb ha
    | true =>
      simp only [d312542, d44713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81613 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312543 q = 1) : d44714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d312543, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312543, d44714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312544 q = 1) : d44715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d312544, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312544, d44715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312545 q = 1) : d44721 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d312545, d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312545, d44721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312546 q = 1) : d44730 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312546, d44730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312546, d44730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312547 q = 1) : d44731 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312547, d44731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312547, d44731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81615 (p : Pattern) (ha : d310774 p = 1) (hb : d312553 p = 1) : d44813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312548 q = 1) : d44732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312548, d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81614 q ha hb
    | true =>
      simp only [d312548, d44732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312549 q = 1) : d44733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312549, d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312549, d44733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312550 q = 1) : d44810 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312550, d44810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312550, d44810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312551 q = 1) : d44811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312551, d44811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312551, d44811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312552 q = 1) : d44812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312552, d44812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312552, d44812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312553 q = 1) : d44813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312553, d44813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312553, d44813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81616 (p : Pattern) (ha : d310774 p = 1) (hb : d312559 p = 1) : d309706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312554 q = 1) : d309701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312554, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81610 q ha hb
    | true =>
      simp only [d312554, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81615 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312555 q = 1) : d309702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312555, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312555, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312556 q = 1) : d309703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312556, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312556, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312557 q = 1) : d309704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312557, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312557, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312558 q = 1) : d309705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312558, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312558, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312559 q = 1) : d309706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312559, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312559, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81617 (p : Pattern) (ha : d310774 p = 1) (hb : d312565 p = 1) : d309712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35481 q = 1) (hb : d310774 q = 1) : d44515 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d35481, d44515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81242 q ha hb
    | true =>
      simp only [d35481, d44515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81245 q ha hb
  have h2 (q : Pattern) (ha : d35482 q = 1) (hb : d310774 q = 1) : d44516 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d35482, d44516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35482, d44516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312514 q = 1) : d309693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312514, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312514, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312515 q = 1) : d309694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312515, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312515, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312517 q = 1) : d309696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312517, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312517, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81608 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312518 q = 1) : d309697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312518, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312518, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312519 q = 1) : d309698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312519, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312519, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312520 q = 1) : d309699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312520, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312520, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312521 q = 1) : d309700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312521, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312521, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312560 q = 1) : d309707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312560, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312560, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81616 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312561 q = 1) : d309708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312561, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312561, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312562 q = 1) : d309709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312562, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312562, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312563 q = 1) : d309710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312563, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312563, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312564 q = 1) : d309711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312564, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312564, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312565 q = 1) : d309712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312565, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312565, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro81618 (p : Pattern) (ha : d310774 p = 1) (hb : d312571 p = 1) : d309718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312566 q = 1) : d309713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312566, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312566, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81617 q ha hb
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312567 q = 1) : d309714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312567, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312567, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312568 q = 1) : d309715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312568, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312568, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312569 q = 1) : d309716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312569, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312569, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312570 q = 1) : d309717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312570, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312570, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312571 q = 1) : d309718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312571, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312571, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81619 (p : Pattern) (ha : d310774 p = 1) (hb : d312577 p = 1) : d312760 p = 1 := by
  have h0 (q : Pattern) (ha : d310774 q = 1) (hb : d312426 q = 1) : d312671 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312426, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81591 q ha hb
    | true =>
      simp only [d312426, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81595 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312453 q = 1) : d312698 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312453, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312453, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81599 q ha hb
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312454 q = 1) : d312699 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312454, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312454, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312481 q = 1) : d312726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312481, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312481, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81603 q ha hb
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312482 q = 1) : d312727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312482, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312482, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312483 q = 1) : d312728 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312483, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312483, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310774 q = 1) (hb : d312510 q = 1) : d312755 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312510, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312510, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81607 q ha hb
  have h8 (q : Pattern) (ha : d310774 q = 1) (hb : d312511 q = 1) : d312756 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312511, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312511, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310774 q = 1) (hb : d312512 q = 1) : d312757 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312512, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312512, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310774 q = 1) (hb : d312513 q = 1) : d312758 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312513, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312513, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d310774 q = 1) (hb : d312572 q = 1) : d309719 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312572, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312572, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81618 q ha hb
  have h12 (q : Pattern) (ha : d310774 q = 1) (hb : d312573 q = 1) : d309720 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312573, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312573, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d310774 q = 1) (hb : d312574 q = 1) : d309721 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312574, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312574, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d310774 q = 1) (hb : d312575 q = 1) : d309722 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312575, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312575, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d310774 q = 1) (hb : d312576 q = 1) : d312759 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d312576, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312576, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d310774 q = 1) (hb : d312577 q = 1) : d312760 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d312577, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312577, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro81620 (p : Pattern) (ha : d310774 p = 1) (hb : d312583 p = 1) : d312766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312578 q = 1) : d312761 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d312578, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81619 q ha hb
    | true =>
      simp only [d312578, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312579 q = 1) : d312762 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d312579, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312579, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312580 q = 1) : d312763 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d312580, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312580, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312581 q = 1) : d312764 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d312581, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312581, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312582 q = 1) : d312765 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d312582, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312582, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312583 q = 1) : d312766 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d312583, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312583, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81621 (p : Pattern) (ha : d310774 p = 1) (hb : d312589 p = 1) : d312772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312584 q = 1) : d312767 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d312584, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81620 q ha hb
    | true =>
      simp only [d312584, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312585 q = 1) : d312768 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d312585, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312585, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312586 q = 1) : d312769 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d312586, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312586, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312587 q = 1) : d312770 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d312587, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312587, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312588 q = 1) : d312771 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d312588, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312588, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312589 q = 1) : d312772 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d312589, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312589, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81622 (p : Pattern) (ha : d310774 p = 1) (hb : d312595 p = 1) : d312778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312590 q = 1) : d312773 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d312590, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81621 q ha hb
    | true =>
      simp only [d312590, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312591 q = 1) : d312774 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d312591, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312591, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312592 q = 1) : d312775 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d312592, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312592, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312593 q = 1) : d312776 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d312593, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312593, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312594 q = 1) : d312777 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d312594, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312594, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312595 q = 1) : d312778 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d312595, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312595, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81623 (p : Pattern) (ha : d310774 p = 1) (hb : d312601 p = 1) : d312784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312596 q = 1) : d312779 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d312596, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81622 q ha hb
    | true =>
      simp only [d312596, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312597 q = 1) : d312780 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d312597, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312597, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312598 q = 1) : d312781 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d312598, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312598, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312599 q = 1) : d312782 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d312599, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312599, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312600 q = 1) : d312783 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d312600, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312600, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312601 q = 1) : d312784 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d312601, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312601, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81624 (p : Pattern) (ha : d310774 p = 1) (hb : d312607 p = 1) : d312790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312602 q = 1) : d312785 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d312602, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81623 q ha hb
    | true =>
      simp only [d312602, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312603 q = 1) : d312786 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d312603, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312603, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312604 q = 1) : d312787 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d312604, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312604, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312605 q = 1) : d312788 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d312605, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312605, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312606 q = 1) : d312789 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d312606, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312606, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312607 q = 1) : d312790 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d312607, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312607, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81625 (p : Pattern) (ha : d310774 p = 1) (hb : d312613 p = 1) : d312796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312608 q = 1) : d312791 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d312608, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81624 q ha hb
    | true =>
      simp only [d312608, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312609 q = 1) : d312792 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d312609, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312609, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312610 q = 1) : d312793 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d312610, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312610, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312611 q = 1) : d312794 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d312611, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312611, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312612 q = 1) : d312795 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d312612, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312612, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312613 q = 1) : d312796 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d312613, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312613, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81626 (p : Pattern) (ha : d310774 p = 1) (hb : d312619 p = 1) : d312802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310774 q = 1) (hb : d312614 q = 1) : d312797 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d312614, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81625 q ha hb
    | true =>
      simp only [d312614, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d310774 q = 1) (hb : d312615 q = 1) : d312798 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d312615, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312615, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d310774 q = 1) (hb : d312616 q = 1) : d312799 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d312616, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312616, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d310774 q = 1) (hb : d312617 q = 1) : d312800 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d312617, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312617, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d310774 q = 1) (hb : d312618 q = 1) : d312801 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d312618, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312618, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d310774 q = 1) (hb : d312619 q = 1) : d312802 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d312619, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312619, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81627 (p : Pattern) (ha : d306197 p = 1) (hb : d310865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306064 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81307 q ha hb
    | true =>
      simp only [d306064, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d306187 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306187, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306194 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306194, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306195 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306195, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306196 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306196, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306197 q = 1) (hb : d310865 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306197, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306197, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81628 (p : Pattern) (ha : d306216 p = 1) (hb : d310872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306064 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81307 q ha hb
    | true =>
      simp only [d306064, d310801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d306187 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306187, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306194 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306194, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306195 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306195, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306196 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306196, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306202 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306206 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306071 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81309 q ha hb
    | true =>
      simp only [d306071, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d306209 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306209, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306213 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306213, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306214 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306214, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306214, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306215 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306215, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306215, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306216 q = 1) (hb : d310872 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306216, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306216, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81629 (p : Pattern) (ha : d306225 p = 1) (hb : d312622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306071 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81309 q ha hb
    | true =>
      simp only [d306071, d310808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d306209 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306209, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306213 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306213, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306223 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306223, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306223, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306224 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306224, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306224, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306225 q = 1) (hb : d312622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306225, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306225, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81630 (p : Pattern) (ha : d306265 p = 1) (hb : d312632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306107 q = 1) (hb : d310844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306107, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81314 q ha hb
    | true =>
      simp only [d306107, d310844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d306255 q = 1) (hb : d312628 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306255, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306255, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306261 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306262 q = 1) (hb : d312629 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306262, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306262, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306263 q = 1) (hb : d312630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306263, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306263, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306264 q = 1) (hb : d312631 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306264, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306264, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306265 q = 1) (hb : d312632 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306265, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306265, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81631 (p : Pattern) (ha : d306271 p = 1) (hb : d312638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306217 q = 1) (hb : d310873 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306217, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81627 q ha hb
    | true =>
      simp only [d306217, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81628 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306220 q = 1) (hb : d310874 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306220, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306220, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306221 q = 1) (hb : d312620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306221, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306221, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306222 q = 1) (hb : d312621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306222, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306222, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306226 q = 1) (hb : d312623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306226, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306226, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81629 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306227 q = 1) (hb : d312624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306227, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306227, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306228 q = 1) (hb : d312625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306228, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306228, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306229 q = 1) (hb : d312626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306229, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306229, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306230 q = 1) (hb : d312627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306230, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306230, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306266 q = 1) (hb : d312633 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306266, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306266, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81630 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306267 q = 1) (hb : d312634 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306267, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306267, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306268 q = 1) (hb : d312635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306268, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306268, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306269 q = 1) (hb : d312636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306269, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306269, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306270 q = 1) (hb : d312637 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306270, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306270, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306271 q = 1) (hb : d312638 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306271, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306271, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81632 (p : Pattern) (ha : d306277 p = 1) (hb : d312644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d306119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80480 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d306120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d306121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d306122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d306123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306272 q = 1) (hb : d312639 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306272, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306272, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81631 q ha hb
  have h8 (q : Pattern) (ha : d306273 q = 1) (hb : d312640 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306273, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306273, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306274 q = 1) (hb : d312641 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306274, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306274, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306275 q = 1) (hb : d312642 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306275, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306275, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306276 q = 1) (hb : d312643 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306276, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306276, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306277 q = 1) (hb : d312644 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306277, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d306277, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro81633 (p : Pattern) (ha : d306394 p = 1) (hb : d311036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306295 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81345 q ha hb
    | true =>
      simp only [d306295, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81346 q ha hb
  have h5 (q : Pattern) (ha : d306384 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306384, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306391 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306391, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306392 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306392, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306393 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306393, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306394 q = 1) (hb : d311036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306394, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306394, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81634 (p : Pattern) (ha : d306415 p = 1) (hb : d311046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306295 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81345 q ha hb
    | true =>
      simp only [d306295, d311031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81346 q ha hb
  have h4 (q : Pattern) (ha : d306384 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306384, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306391 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306391, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306392 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306392, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306393 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306393, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306400 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306405 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306305 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81348 q ha hb
    | true =>
      simp only [d306305, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81349 q ha hb
  have h13 (q : Pattern) (ha : d306408 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306408, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306412 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306412, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306413 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306413, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306413, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306414 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306414, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306414, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306415 q = 1) (hb : d311046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306415, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306415, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81635 (p : Pattern) (ha : d306435 p = 1) (hb : d312647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306305 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81348 q ha hb
    | true =>
      simp only [d306305, d311041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81349 q ha hb
  have h3 (q : Pattern) (ha : d306408 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306408, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306412 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306412, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306433 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306433, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306433, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306434 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306434, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306434, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306435 q = 1) (hb : d312647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306435, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306435, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81636 (p : Pattern) (ha : d306503 p = 1) (hb : d312658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306492 q = 1) (hb : d312653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306492, d312653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81383 q ha hb
    | true =>
      simp only [d306492, d312653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81386 q ha hb
  have h3 (q : Pattern) (ha : d306493 q = 1) (hb : d312654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306493, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306493, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306500 q = 1) (hb : d312655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306500, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306500, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306501 q = 1) (hb : d312656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306501, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306501, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306502 q = 1) (hb : d312657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306502, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306502, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306503 q = 1) (hb : d312658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306503, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306503, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81637 (p : Pattern) (ha : d306516 p = 1) (hb : d312664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306416 q = 1) (hb : d311047 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306416, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81633 q ha hb
    | true =>
      simp only [d306416, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306430 q = 1) (hb : d311048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306430, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306430, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306431 q = 1) (hb : d312645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306431, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306431, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306432 q = 1) (hb : d312646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306432, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306432, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306436 q = 1) (hb : d312648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306436, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306436, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306438 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306439 q = 1) (hb : d312649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306439, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306439, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306440 q = 1) (hb : d312650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306440, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306440, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306441 q = 1) (hb : d312651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306441, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306441, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306442 q = 1) (hb : d312652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306442, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306442, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306504 q = 1) (hb : d312659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306504, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306504, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306512 q = 1) (hb : d312660 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306512, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306512, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306513 q = 1) (hb : d312661 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306513, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306513, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306514 q = 1) (hb : d312662 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306514, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306514, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306515 q = 1) (hb : d312663 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306515, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306515, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306516 q = 1) (hb : d312664 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306516, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306516, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81638 (p : Pattern) (ha : d306522 p = 1) (hb : d312670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306517 q = 1) (hb : d312665 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306517, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306517, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81637 q ha hb
  have h2 (q : Pattern) (ha : d306518 q = 1) (hb : d312666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306518, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306518, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306519 q = 1) (hb : d312667 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306519, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306519, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306520 q = 1) (hb : d312668 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306520, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306520, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306521 q = 1) (hb : d312669 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306521, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306521, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306522 q = 1) (hb : d312670 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306522, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306522, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81639 (p : Pattern) (ha : d306670 p = 1) (hb : d311295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306559 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81396 q ha hb
    | true =>
      simp only [d306559, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81397 q ha hb
  have h5 (q : Pattern) (ha : d306660 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306660, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306667 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306667, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306668 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306668, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306669 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306669, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306670 q = 1) (hb : d311295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306670, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306670, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81640 (p : Pattern) (ha : d306691 p = 1) (hb : d311305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306559 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81396 q ha hb
    | true =>
      simp only [d306559, d311290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81397 q ha hb
  have h4 (q : Pattern) (ha : d306660 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306660, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306667 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306667, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306668 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306668, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306669 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306669, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306676 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306681 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306569 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81399 q ha hb
    | true =>
      simp only [d306569, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81400 q ha hb
  have h13 (q : Pattern) (ha : d306684 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306684, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306688 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306688, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306689 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306689, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306689, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306690 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306690, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306690, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306691 q = 1) (hb : d311305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306691, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306691, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81641 (p : Pattern) (ha : d306711 p = 1) (hb : d312674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306569 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81399 q ha hb
    | true =>
      simp only [d306569, d311300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81400 q ha hb
  have h3 (q : Pattern) (ha : d306684 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306684, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306688 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306688, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306709 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306709, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306709, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306710 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306710, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306710, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306711 q = 1) (hb : d312674 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306711, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306711, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81642 (p : Pattern) (ha : d306796 p = 1) (hb : d312685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306785 q = 1) (hb : d312680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306785, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81438 q ha hb
    | true =>
      simp only [d306785, d312680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81441 q ha hb
  have h3 (q : Pattern) (ha : d306786 q = 1) (hb : d312681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306786, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306786, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306793 q = 1) (hb : d312682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306793, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306793, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306794 q = 1) (hb : d312683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306794, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306794, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306795 q = 1) (hb : d312684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306795, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306795, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306796 q = 1) (hb : d312685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306796, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306796, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81643 (p : Pattern) (ha : d306809 p = 1) (hb : d312691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306692 q = 1) (hb : d311306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306692, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81639 q ha hb
    | true =>
      simp only [d306692, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81640 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306706 q = 1) (hb : d311307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306706, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306706, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306707 q = 1) (hb : d312672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306707, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306707, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306708 q = 1) (hb : d312673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306708, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306708, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306712 q = 1) (hb : d312675 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306712, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306712, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81641 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306715 q = 1) (hb : d312676 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306715, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306715, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306716 q = 1) (hb : d312677 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306716, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306716, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306717 q = 1) (hb : d312678 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306717, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306717, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306718 q = 1) (hb : d312679 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306718, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306718, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306797 q = 1) (hb : d312686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306797, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306797, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81642 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306804 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306805 q = 1) (hb : d312687 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306805, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306805, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306806 q = 1) (hb : d312688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306806, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306806, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306807 q = 1) (hb : d312689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306807, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306807, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306808 q = 1) (hb : d312690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306808, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306808, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306809 q = 1) (hb : d312691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306809, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306809, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81644 (p : Pattern) (ha : d306815 p = 1) (hb : d312697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306810 q = 1) (hb : d312692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306810, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306810, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81643 q ha hb
  have h2 (q : Pattern) (ha : d306811 q = 1) (hb : d312693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306811, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306811, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306812 q = 1) (hb : d312694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306812, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306812, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306813 q = 1) (hb : d312695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306813, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306813, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306814 q = 1) (hb : d312696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306814, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306814, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306815 q = 1) (hb : d312697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306815, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306815, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81645 (p : Pattern) (ha : d307028 p = 1) (hb : d311633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306909 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81456 q ha hb
    | true =>
      simp only [d306909, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81457 q ha hb
  have h5 (q : Pattern) (ha : d307009 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307009, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307025 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307025, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307026 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307026, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307027 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307027, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307028 q = 1) (hb : d311633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307028, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307028, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81646 (p : Pattern) (ha : d307049 p = 1) (hb : d311643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306909 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81456 q ha hb
    | true =>
      simp only [d306909, d311628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81457 q ha hb
  have h4 (q : Pattern) (ha : d307009 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307009, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307025 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307025, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307026 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307026, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307027 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307027, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306919 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81459 q ha hb
    | true =>
      simp only [d306919, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81460 q ha hb
  have h13 (q : Pattern) (ha : d307042 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307042, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307046 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307046, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307047 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307047, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307047, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307048 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307048, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307048, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307049 q = 1) (hb : d311643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307049, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307049, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81647 (p : Pattern) (ha : d307069 p = 1) (hb : d312702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306919 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81459 q ha hb
    | true =>
      simp only [d306919, d311638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81460 q ha hb
  have h3 (q : Pattern) (ha : d307042 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307042, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307046 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307046, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307067 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307067, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307067, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307068 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307068, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307068, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307069 q = 1) (hb : d312702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307069, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307069, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81648 (p : Pattern) (ha : d307190 p = 1) (hb : d312713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307170 q = 1) (hb : d312708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307170, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81500 q ha hb
    | true =>
      simp only [d307170, d312708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81505 q ha hb
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d312709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307171, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307187 q = 1) (hb : d312710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307188 q = 1) (hb : d312711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307189 q = 1) (hb : d312712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307190 q = 1) (hb : d312713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81649 (p : Pattern) (ha : d307203 p = 1) (hb : d312719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307050 q = 1) (hb : d311644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81645 q ha hb
    | true =>
      simp only [d307050, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81646 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307064 q = 1) (hb : d311645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307064, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307065 q = 1) (hb : d312700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307065, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307066 q = 1) (hb : d312701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307066, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307070 q = 1) (hb : d312703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307070, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81647 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307073 q = 1) (hb : d312704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307073, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307074 q = 1) (hb : d312705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307074, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307075 q = 1) (hb : d312706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307075, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307076 q = 1) (hb : d312707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307076, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307191 q = 1) (hb : d312714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307191, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81648 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307199 q = 1) (hb : d312715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307199, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307200 q = 1) (hb : d312716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307200, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307201 q = 1) (hb : d312717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307201, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307202 q = 1) (hb : d312718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307202, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307203 q = 1) (hb : d312719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307203, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81650 (p : Pattern) (ha : d307209 p = 1) (hb : d312725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d312720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81649 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d312721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d312722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d312723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d312724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d312725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81651 (p : Pattern) (ha : d307443 p = 1) (hb : d312026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307324 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
    | true =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
  have h5 (q : Pattern) (ha : d307411 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307411, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307440 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307440, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307441 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307441, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307442 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307442, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307443 q = 1) (hb : d312026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307443, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307443, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81652 (p : Pattern) (ha : d307464 p = 1) (hb : d312036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307324 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81525 q ha hb
    | true =>
      simp only [d307324, d312021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81526 q ha hb
  have h4 (q : Pattern) (ha : d307411 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307411, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307440 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307440, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307441 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307441, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307442 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307442, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307449 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307334 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81528 q ha hb
    | true =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81529 q ha hb
  have h13 (q : Pattern) (ha : d307457 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307457, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307461 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307461, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307462 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307462, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307462, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307463 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307463, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307463, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307464 q = 1) (hb : d312036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307464, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307464, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81653 (p : Pattern) (ha : d307484 p = 1) (hb : d312731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307334 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81528 q ha hb
    | true =>
      simp only [d307334, d312031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81529 q ha hb
  have h3 (q : Pattern) (ha : d307457 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307457, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307461 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307461, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307482 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307482, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307482, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307483 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307483, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307483, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307484 q = 1) (hb : d312731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81654 (p : Pattern) (ha : d307616 p = 1) (hb : d312742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307585 q = 1) (hb : d312737 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307585, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81570 q ha hb
    | true =>
      simp only [d307585, d312737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81576 q ha hb
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d312738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307613 q = 1) (hb : d312739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307614 q = 1) (hb : d312740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307615 q = 1) (hb : d312741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307616 q = 1) (hb : d312742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81655 (p : Pattern) (ha : d307629 p = 1) (hb : d312748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307465 q = 1) (hb : d312037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81651 q ha hb
    | true =>
      simp only [d307465, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81652 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307479 q = 1) (hb : d312038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307479, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307480 q = 1) (hb : d312729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307480, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307481 q = 1) (hb : d312730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307481, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307485 q = 1) (hb : d312732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307485, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81653 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307488 q = 1) (hb : d312733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307488, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307489 q = 1) (hb : d312734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307489, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307490 q = 1) (hb : d312735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307490, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307491 q = 1) (hb : d312736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307491, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307617 q = 1) (hb : d312743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307617, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81654 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307625 q = 1) (hb : d312744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307625, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307626 q = 1) (hb : d312745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307626, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307627 q = 1) (hb : d312746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307627, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307628 q = 1) (hb : d312747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307628, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307629 q = 1) (hb : d312748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307629, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81656 (p : Pattern) (ha : d307635 p = 1) (hb : d312754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d312749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81655 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d312750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d312751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d312752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d312753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d312754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81657 (p : Pattern) (ha : d307931 p = 1) (hb : d312760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d312671 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81632 q ha hb
    | true =>
      simp only [d306523, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81638 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d312698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81644 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d312699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d312726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81650 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d312727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d312728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d312755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81656 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d312756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d312757 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d312758 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80516 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d312759 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d312760 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro81658 (p : Pattern) (ha : d307937 p = 1) (hb : d312766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d312761 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81657 q ha hb
    | true =>
      simp only [d307932, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d312762 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d312763 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d312764 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d312765 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d312766 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81659 (p : Pattern) (ha : d307943 p = 1) (hb : d312772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d312767 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81658 q ha hb
    | true =>
      simp only [d307938, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d312768 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d312769 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d312770 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d312771 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d312772 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81660 (p : Pattern) (ha : d307949 p = 1) (hb : d312778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d312773 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81659 q ha hb
    | true =>
      simp only [d307944, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d312774 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d312775 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d312776 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d312777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d312778 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81661 (p : Pattern) (ha : d307955 p = 1) (hb : d312784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d312779 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81660 q ha hb
    | true =>
      simp only [d307950, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d312780 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d312781 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d312782 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d312783 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d312784 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81662 (p : Pattern) (ha : d307961 p = 1) (hb : d312790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d312785 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81661 q ha hb
    | true =>
      simp only [d307956, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d312786 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d312787 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d312788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d312789 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d312790 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81663 (p : Pattern) (ha : d307967 p = 1) (hb : d312796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d312791 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81662 q ha hb
    | true =>
      simp only [d307962, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d312792 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d312793 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d312794 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d312795 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d312796 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81664 (p : Pattern) (ha : d307973 p = 1) (hb : d312802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d312797 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81663 q ha hb
    | true =>
      simp only [d307968, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d312798 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d312799 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d312800 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d312801 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d312802 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro81665 (p : Pattern) (ha : d309809 p = 1) (hb : d310865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309805 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309805, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309806 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309806, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309807 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309807, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309808 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309808, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309809 q = 1) (hb : d310865 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309809, d310865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81666 (p : Pattern) (ha : d309814 p = 1) (hb : d310872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310801 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309805 q = 1) (hb : d310861 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309805, d310861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309806 q = 1) (hb : d310862 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309806, d310862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309807 q = 1) (hb : d310863 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309807, d310863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309808 q = 1) (hb : d310864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309808, d310864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42445 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309810 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309810, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309811 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309811, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309812 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309812, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309813 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309813, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309814 q = 1) (hb : d310872 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309814, d310872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81667 (p : Pattern) (ha : d309821 p = 1) (hb : d312622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309810 q = 1) (hb : d310868 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309810, d310868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309811 q = 1) (hb : d310869 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309811, d310869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309819 q = 1) (hb : d310870 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309819, d310870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309820 q = 1) (hb : d310871 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309820, d310871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309821 q = 1) (hb : d312622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309821, d312622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81668 (p : Pattern) (ha : d309831 p = 1) (hb : d312632 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309827 q = 1) (hb : d312628 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309827, d312628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309828 q = 1) (hb : d312629 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309828, d312629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309829 q = 1) (hb : d312630 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309829, d312630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309830 q = 1) (hb : d312631 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309830, d312631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309831 q = 1) (hb : d312632 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309831, d312632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81669 (p : Pattern) (ha : d309837 p = 1) (hb : d312638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309815 q = 1) (hb : d310873 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81665 q ha hb
    | true =>
      simp only [d309815, d310873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81666 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309816 q = 1) (hb : d310874 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309816, d310874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309817 q = 1) (hb : d312620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309817, d312620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309818 q = 1) (hb : d312621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309818, d312621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309822 q = 1) (hb : d312623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309822, d312623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81667 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309823 q = 1) (hb : d312624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309823, d312624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309824 q = 1) (hb : d312625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309824, d312625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309825 q = 1) (hb : d312626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309825, d312626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309826 q = 1) (hb : d312627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309826, d312627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309832 q = 1) (hb : d312633 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309832, d312633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81668 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309833 q = 1) (hb : d312634 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309833, d312634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309834 q = 1) (hb : d312635 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309834, d312635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309835 q = 1) (hb : d312636 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309835, d312636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309836 q = 1) (hb : d312637 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309836, d312637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309837 q = 1) (hb : d312638 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309837, d312638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81670 (p : Pattern) (ha : d309843 p = 1) (hb : d312644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d309800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80535 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d309801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d309802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d309804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309838 q = 1) (hb : d312639 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309838, d312639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81669 q ha hb
  have h8 (q : Pattern) (ha : d309839 q = 1) (hb : d312640 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309839, d312640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309840 q = 1) (hb : d312641 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309840, d312641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309841 q = 1) (hb : d312642 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309841, d312642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309842 q = 1) (hb : d312643 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309842, d312643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309843 q = 1) (hb : d312644 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d309843, d312644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro81671 (p : Pattern) (ha : d309848 p = 1) (hb : d311036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309844 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309844, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309845 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309845, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309846 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309846, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309847 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309847, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309848 q = 1) (hb : d311036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309848, d311036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81672 (p : Pattern) (ha : d309853 p = 1) (hb : d311046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311031 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309844 q = 1) (hb : d311032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309844, d311032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309845 q = 1) (hb : d311033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309845, d311033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309846 q = 1) (hb : d311034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309846, d311034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309847 q = 1) (hb : d311035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309847, d311035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42705 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309849 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309849, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309850 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309850, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309851 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309851, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309852 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309852, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309853 q = 1) (hb : d311046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309853, d311046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81673 (p : Pattern) (ha : d309860 p = 1) (hb : d312647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311041 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309849 q = 1) (hb : d311042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309849, d311042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309850 q = 1) (hb : d311043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309850, d311043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309858 q = 1) (hb : d311044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309858, d311044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309859 q = 1) (hb : d311045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309859, d311045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309860 q = 1) (hb : d312647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309860, d312647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81674 (p : Pattern) (ha : d309870 p = 1) (hb : d312658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312653 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309866 q = 1) (hb : d312654 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309866, d312654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309867 q = 1) (hb : d312655 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309867, d312655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309868 q = 1) (hb : d312656 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309868, d312656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309869 q = 1) (hb : d312657 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309869, d312657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309870 q = 1) (hb : d312658 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309870, d312658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81675 (p : Pattern) (ha : d309876 p = 1) (hb : d312664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309854 q = 1) (hb : d311047 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81671 q ha hb
    | true =>
      simp only [d309854, d311047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81672 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309855 q = 1) (hb : d311048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309855, d311048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309856 q = 1) (hb : d312645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309856, d312645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309857 q = 1) (hb : d312646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309857, d312646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309861 q = 1) (hb : d312648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309861, d312648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81673 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42746 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309862 q = 1) (hb : d312649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309862, d312649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309863 q = 1) (hb : d312650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309863, d312650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309864 q = 1) (hb : d312651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309864, d312651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309865 q = 1) (hb : d312652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309865, d312652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309871 q = 1) (hb : d312659 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309871, d312659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81674 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309872 q = 1) (hb : d312660 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309872, d312660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309873 q = 1) (hb : d312661 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309873, d312661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309874 q = 1) (hb : d312662 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309874, d312662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309875 q = 1) (hb : d312663 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309875, d312663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309876 q = 1) (hb : d312664 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309876, d312664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81676 (p : Pattern) (ha : d309882 p = 1) (hb : d312670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309877 q = 1) (hb : d312665 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309877, d312665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81675 q ha hb
  have h2 (q : Pattern) (ha : d309878 q = 1) (hb : d312666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309878, d312666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309879 q = 1) (hb : d312667 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309879, d312667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309880 q = 1) (hb : d312668 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309880, d312668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309881 q = 1) (hb : d312669 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309881, d312669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309882 q = 1) (hb : d312670 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309882, d312670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81677 (p : Pattern) (ha : d309888 p = 1) (hb : d311295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309884 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309884, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309885 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309885, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309886 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309886, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309887 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309887, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309888 q = 1) (hb : d311295 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309888, d311295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81678 (p : Pattern) (ha : d309893 p = 1) (hb : d311305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311290 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309884 q = 1) (hb : d311291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309884, d311291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309885 q = 1) (hb : d311292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309885, d311292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309886 q = 1) (hb : d311293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309886, d311293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309887 q = 1) (hb : d311294 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309887, d311294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43091 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309889 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309889, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309890 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309890, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309891 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309891, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309892 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309892, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309893 q = 1) (hb : d311305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309893, d311305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81679 (p : Pattern) (ha : d309900 p = 1) (hb : d312674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311300 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309889 q = 1) (hb : d311301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309889, d311301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309890 q = 1) (hb : d311302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309890, d311302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309898 q = 1) (hb : d311303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309898, d311303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309899 q = 1) (hb : d311304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309899, d311304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309900 q = 1) (hb : d312674 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309900, d312674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81680 (p : Pattern) (ha : d309910 p = 1) (hb : d312685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312680 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309906 q = 1) (hb : d312681 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309906, d312681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309907 q = 1) (hb : d312682 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309907, d312682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309908 q = 1) (hb : d312683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309908, d312683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309909 q = 1) (hb : d312684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309909, d312684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309910 q = 1) (hb : d312685 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309910, d312685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81681 (p : Pattern) (ha : d309916 p = 1) (hb : d312691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309894 q = 1) (hb : d311306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81677 q ha hb
    | true =>
      simp only [d309894, d311306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81678 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309895 q = 1) (hb : d311307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309895, d311307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309896 q = 1) (hb : d312672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309896, d312672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309897 q = 1) (hb : d312673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309897, d312673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309901 q = 1) (hb : d312675 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309901, d312675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81679 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309902 q = 1) (hb : d312676 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309902, d312676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309903 q = 1) (hb : d312677 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309903, d312677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309904 q = 1) (hb : d312678 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309904, d312678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309905 q = 1) (hb : d312679 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309905, d312679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309911 q = 1) (hb : d312686 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309911, d312686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81680 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309912 q = 1) (hb : d312687 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309912, d312687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309913 q = 1) (hb : d312688 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309913, d312688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309914 q = 1) (hb : d312689 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309914, d312689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309915 q = 1) (hb : d312690 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309915, d312690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309916 q = 1) (hb : d312691 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309916, d312691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81682 (p : Pattern) (ha : d309922 p = 1) (hb : d312697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309917 q = 1) (hb : d312692 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309917, d312692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81681 q ha hb
  have h2 (q : Pattern) (ha : d309918 q = 1) (hb : d312693 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309918, d312693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309919 q = 1) (hb : d312694 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309919, d312694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309920 q = 1) (hb : d312695 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309920, d312695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309921 q = 1) (hb : d312696 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309921, d312696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309922 q = 1) (hb : d312697 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309922, d312697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81683 (p : Pattern) (ha : d309929 p = 1) (hb : d311633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309925 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309925, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309926 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309926, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309927 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309927, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309928 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309928, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309929 q = 1) (hb : d311633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309929, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309929, d311633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81684 (p : Pattern) (ha : d309934 p = 1) (hb : d311643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d311628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309925 q = 1) (hb : d311629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309925, d311629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309926 q = 1) (hb : d311630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309926, d311630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309927 q = 1) (hb : d311631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309927, d311631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309928 q = 1) (hb : d311632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309928, d311632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309930 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309930, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309931 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309931, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309932 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309932, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309932, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309933 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309933, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309933, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309934 q = 1) (hb : d311643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309934, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309934, d311643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81685 (p : Pattern) (ha : d309941 p = 1) (hb : d312702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d311638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309930 q = 1) (hb : d311639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309930, d311639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309931 q = 1) (hb : d311640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309931, d311640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309939 q = 1) (hb : d311641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309939, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309939, d311641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309940 q = 1) (hb : d311642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309940, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309940, d311642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309941 q = 1) (hb : d312702 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309941, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309941, d312702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81686 (p : Pattern) (ha : d309951 p = 1) (hb : d312713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309947 q = 1) (hb : d312709 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309947, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309947, d312709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309948 q = 1) (hb : d312710 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309948, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309948, d312710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309949 q = 1) (hb : d312711 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309949, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309949, d312711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309950 q = 1) (hb : d312712 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309950, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309950, d312712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309951 q = 1) (hb : d312713 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309951, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309951, d312713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81687 (p : Pattern) (ha : d309957 p = 1) (hb : d312719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309935 q = 1) (hb : d311644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309935, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81683 q ha hb
    | true =>
      simp only [d309935, d311644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81684 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309936 q = 1) (hb : d311645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309936, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309936, d311645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309937 q = 1) (hb : d312700 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309937, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309937, d312700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309938 q = 1) (hb : d312701 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309938, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309938, d312701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309942 q = 1) (hb : d312703 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309942, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309942, d312703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81685 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43646 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309943 q = 1) (hb : d312704 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309943, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309943, d312704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309944 q = 1) (hb : d312705 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309944, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309944, d312705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309945 q = 1) (hb : d312706 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309945, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309945, d312706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309946 q = 1) (hb : d312707 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309946, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309946, d312707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309952 q = 1) (hb : d312714 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309952, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309952, d312714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81686 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309953 q = 1) (hb : d312715 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309953, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309953, d312715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309954 q = 1) (hb : d312716 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309954, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309954, d312716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309955 q = 1) (hb : d312717 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309955, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309955, d312717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309956 q = 1) (hb : d312718 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309956, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309956, d312718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309957 q = 1) (hb : d312719 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309957, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309957, d312719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81688 (p : Pattern) (ha : d309963 p = 1) (hb : d312725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309958 q = 1) (hb : d312720 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309958, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309958, d312720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81687 q ha hb
  have h2 (q : Pattern) (ha : d309959 q = 1) (hb : d312721 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309959, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309959, d312721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309960 q = 1) (hb : d312722 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309960, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309960, d312722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309961 q = 1) (hb : d312723 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309961, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309961, d312723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309962 q = 1) (hb : d312724 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309962, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309962, d312724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309963 q = 1) (hb : d312725 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309963, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309963, d312725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81689 (p : Pattern) (ha : d309971 p = 1) (hb : d312026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309967 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309967, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309968 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309968, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309969 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309969, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309970 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309970, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309971 q = 1) (hb : d312026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309971, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309971, d312026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81690 (p : Pattern) (ha : d309976 p = 1) (hb : d312036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d312021 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309967 q = 1) (hb : d312022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309967, d312022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309968 q = 1) (hb : d312023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309968, d312023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309969 q = 1) (hb : d312024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309969, d312024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309970 q = 1) (hb : d312025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309970, d312025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44196 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309972 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309972, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309973 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309973, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309974 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309974, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309974, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309975 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309975, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309975, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309976 q = 1) (hb : d312036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309976, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309976, d312036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro81691 (p : Pattern) (ha : d309983 p = 1) (hb : d312731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312031 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309972 q = 1) (hb : d312032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309972, d312032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309973 q = 1) (hb : d312033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309973, d312033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309981 q = 1) (hb : d312034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309981, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309981, d312034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309982 q = 1) (hb : d312035 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309982, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309982, d312035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309983 q = 1) (hb : d312731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309983, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309983, d312731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81692 (p : Pattern) (ha : d309993 p = 1) (hb : d312742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d312737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309989 q = 1) (hb : d312738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309989, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309989, d312738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309990 q = 1) (hb : d312739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309990, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309990, d312739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309991 q = 1) (hb : d312740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309991, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309991, d312740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309992 q = 1) (hb : d312741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309992, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309992, d312741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309993 q = 1) (hb : d312742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309993, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309993, d312742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81693 (p : Pattern) (ha : d309999 p = 1) (hb : d312748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309977 q = 1) (hb : d312037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309977, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81689 q ha hb
    | true =>
      simp only [d309977, d312037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81690 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309978 q = 1) (hb : d312038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309978, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309978, d312038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309979 q = 1) (hb : d312729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309979, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309979, d312729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309980 q = 1) (hb : d312730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309980, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309980, d312730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309984 q = 1) (hb : d312732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309984, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309984, d312732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81691 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309985 q = 1) (hb : d312733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309985, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309985, d312733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309986 q = 1) (hb : d312734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309986, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309986, d312734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309987 q = 1) (hb : d312735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309987, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309987, d312735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309988 q = 1) (hb : d312736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309988, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309988, d312736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309994 q = 1) (hb : d312743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309994, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309994, d312743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81692 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309995 q = 1) (hb : d312744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309995, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309995, d312744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309996 q = 1) (hb : d312745 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309996, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309996, d312745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309997 q = 1) (hb : d312746 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309997, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309997, d312746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309998 q = 1) (hb : d312747 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309998, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309998, d312747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309999 q = 1) (hb : d312748 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309999, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309999, d312748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81694 (p : Pattern) (ha : d310005 p = 1) (hb : d312754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310000 q = 1) (hb : d312749 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d310000, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310000, d312749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81693 q ha hb
  have h2 (q : Pattern) (ha : d310001 q = 1) (hb : d312750 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d310001, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310001, d312750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310002 q = 1) (hb : d312751 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d310002, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310002, d312751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310003 q = 1) (hb : d312752 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d310003, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310003, d312752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310004 q = 1) (hb : d312753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d310004, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310004, d312753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310005 q = 1) (hb : d312754 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d310005, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310005, d312754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81695 (p : Pattern) (ha : d310011 p = 1) (hb : d312760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d309883 q = 1) (hb : d312671 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81670 q ha hb
    | true =>
      simp only [d309883, d312671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81676 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309923 q = 1) (hb : d312698 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309923, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309923, d312698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81682 q ha hb
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d312699 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309924, d312699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309964 q = 1) (hb : d312726 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309964, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309964, d312726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81688 q ha hb
  have h5 (q : Pattern) (ha : d309965 q = 1) (hb : d312727 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309965, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309965, d312727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309966 q = 1) (hb : d312728 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d312728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310006 q = 1) (hb : d312755 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d310006, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310006, d312755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81694 q ha hb
  have h8 (q : Pattern) (ha : d310007 q = 1) (hb : d312756 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d310007, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310007, d312756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310008 q = 1) (hb : d312757 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d310008, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310008, d312757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310009 q = 1) (hb : d312758 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310009, d312758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309506 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309506, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309506, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80530 q ha hb
  have h12 (q : Pattern) (ha : d309507 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309507, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309507, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309508 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309508, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309508, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309509 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309509, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309509, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d310010 q = 1) (hb : d312759 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d310010, d312759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d310011 q = 1) (hb : d312760 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d310011, d312760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro81696 (p : Pattern) (ha : d310017 p = 1) (hb : d312766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d312761 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81695 q ha hb
    | true =>
      simp only [d310012, d312761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d312762 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d312762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d312763 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d312763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d312764 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d312764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d312765 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d312765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d312766 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d312766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81697 (p : Pattern) (ha : d310023 p = 1) (hb : d312772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d312767 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81696 q ha hb
    | true =>
      simp only [d310018, d312767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d312768 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d312768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d312769 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d312769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d312770 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d312770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d312771 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d312771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310023 q = 1) (hb : d312772 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d312772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81698 (p : Pattern) (ha : d310029 p = 1) (hb : d312778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d312773 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81697 q ha hb
    | true =>
      simp only [d310024, d312773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d312774 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d312774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d312775 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d312775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d312776 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d312776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d312777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d312777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d312778 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d312778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81699 (p : Pattern) (ha : d310035 p = 1) (hb : d312784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d312779 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81698 q ha hb
    | true =>
      simp only [d310030, d312779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d312780 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d312780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d312781 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d312781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d312782 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d312782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d312783 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d312783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d312784 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d312784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81700 (p : Pattern) (ha : d310041 p = 1) (hb : d312790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d312785 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81699 q ha hb
    | true =>
      simp only [d310036, d312785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d312786 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d312786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d312787 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d312787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d312788 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d312788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d312789 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d312789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d312790 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d312790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81701 (p : Pattern) (ha : d310047 p = 1) (hb : d312796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d312791 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81700 q ha hb
    | true =>
      simp only [d310042, d312791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d312792 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d312792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d312793 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d312793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d312794 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d312794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d312795 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d312795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d312796 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d312796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81702 (p : Pattern) (ha : d310053 p = 1) (hb : d312802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d312797 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81701 q ha hb
    | true =>
      simp only [d310048, d312797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d312798 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d312798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d312799 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d312799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d312800 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d312800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d312801 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d312801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d312802 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d312802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81703 (p : Pattern) (ha : d33214 p = 1) (hb : d277739 p = 1) : d277741 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33213 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33213, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17 q = 1) (hb : d277739 q = 1) : d17 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33214 q = 1) (hb : d277739 q = 1) : d277741 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33214, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33214, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81704 (p : Pattern) (ha : d33220 p = 1) (hb : d277739 p = 1) : d277747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81703 q ha hb
    | true =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d277739 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d277739 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d277739 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d277739 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33218 q = 1) (hb : d277739 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33219 q = 1) (hb : d277739 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d277739 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33220 q = 1) (hb : d277739 q = 1) : d277747 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33220, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33220, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81705 (p : Pattern) (ha : d33226 p = 1) (hb : d277739 p = 1) : d277753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33221 q = 1) (hb : d277739 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33222 q = 1) (hb : d277739 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33223 q = 1) (hb : d277739 q = 1) : d277750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33224 q = 1) (hb : d277739 q = 1) : d277751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d277739 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33225 q = 1) (hb : d277739 q = 1) : d277752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33225, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33225, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d277739 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33226 q = 1) (hb : d277739 q = 1) : d277753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33226, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33226, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81706 (p : Pattern) (ha : d33232 p = 1) (hb : d277739 p = 1) : d277759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d277739 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d277739 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
    | true =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d277739 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d277739 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d277739 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33230 q = 1) (hb : d277739 q = 1) : d277757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d277739 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33231 q = 1) (hb : d277739 q = 1) : d277758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33231, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33231, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33232 q = 1) (hb : d277739 q = 1) : d277759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33232, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33232, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro81707 (p : Pattern) (ha : d33238 p = 1) (hb : d277739 p = 1) : d277765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277739 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d277739 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33238 q = 1) (hb : d277739 q = 1) : d277765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33238, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33238, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81708 (p : Pattern) (ha : d265915 p = 1) (hb : d277739 p = 1) : d277771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d277739 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d277739 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d277739 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33239 q = 1) (hb : d277739 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d277739 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277739 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d277739 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d277739 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d277739 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265915 q = 1) (hb : d277739 q = 1) : d277771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265915, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265915, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81709 (p : Pattern) (ha : d33245 p = 1) (hb : d277739 p = 1) : d277772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277739 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d277739 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33245 q = 1) (hb : d277739 q = 1) : d277772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33245, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33245, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro81710 (p : Pattern) (ha : d265920 p = 1) (hb : d277739 p = 1) : d277778 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d277739 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d277739 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d277739 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33239 q = 1) (hb : d277739 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d277739 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277739 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d277739 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d277739 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d277739 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d277739 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d277739 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d277739 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d33246 q = 1) (hb : d277739 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81709 q ha hb
    | true =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265916 q = 1) (hb : d277739 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d277739 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d265917 q = 1) (hb : d277739 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265918 q = 1) (hb : d277739 q = 1) : d277776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265918, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265918, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265919 q = 1) (hb : d277739 q = 1) : d277777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265919, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265919, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d265920 q = 1) (hb : d277739 q = 1) : d277778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265920, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265920, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro81711 (p : Pattern) (ha : d265927 p = 1) (hb : d277739 p = 1) : d277785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d277739 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d277739 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81709 q ha hb
    | true =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265916 q = 1) (hb : d277739 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d277739 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265917 q = 1) (hb : d277739 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265925 q = 1) (hb : d277739 q = 1) : d277783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265925, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265925, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265926 q = 1) (hb : d277739 q = 1) : d277784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265926, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265926, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265927 q = 1) (hb : d277739 q = 1) : d277785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265927, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265927, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81712 (p : Pattern) (ha : d33269 p = 1) (hb : d277739 p = 1) : d277796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33264 q = 1) (hb : d277739 q = 1) : d277791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
  have h2 (q : Pattern) (ha : d33221 q = 1) (hb : d277739 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33265 q = 1) (hb : d277739 q = 1) : d277792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33222 q = 1) (hb : d277739 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33266 q = 1) (hb : d277739 q = 1) : d277793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33267 q = 1) (hb : d277739 q = 1) : d277794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d277739 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33268 q = 1) (hb : d277739 q = 1) : d277795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33268, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33268, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d277739 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33269 q = 1) (hb : d277739 q = 1) : d277796 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33269, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33269, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro81713 (p : Pattern) (ha : d33275 p = 1) (hb : d277739 p = 1) : d277802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d277739 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33270 q = 1) (hb : d277739 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81712 q ha hb
    | true =>
      simp only [d33270, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33271 q = 1) (hb : d277739 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33272 q = 1) (hb : d277739 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d277739 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33273 q = 1) (hb : d277739 q = 1) : d277800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33273, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d277739 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33274 q = 1) (hb : d277739 q = 1) : d277801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33274, d277801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33274, d277801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33275 q = 1) (hb : d277739 q = 1) : d277802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33275, d277802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33275, d277802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro81714 (p : Pattern) (ha : d33281 p = 1) (hb : d277739 p = 1) : d277808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d277739 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81713 q ha hb
    | true =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d277739 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d277739 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33278 q = 1) (hb : d277739 q = 1) : d277805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33278, d277805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33278, d277805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33279 q = 1) (hb : d277739 q = 1) : d277806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33279, d277806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33279, d277806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33280 q = 1) (hb : d277739 q = 1) : d277807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33280, d277807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33280, d277807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33281 q = 1) (hb : d277739 q = 1) : d277808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33281, d277808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33281, d277808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro81715 (p : Pattern) (ha : d265937 p = 1) (hb : d277739 p = 1) : d277814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d277739 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33282 q = 1) (hb : d277739 q = 1) : d277809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81714 q ha hb
    | true =>
      simp only [d33282, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265933 q = 1) (hb : d277739 q = 1) : d277810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265933, d277810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265933, d277810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d277739 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265934 q = 1) (hb : d277739 q = 1) : d277811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265934, d277811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265934, d277811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265935 q = 1) (hb : d277739 q = 1) : d277812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265935, d277812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265935, d277812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265936 q = 1) (hb : d277739 q = 1) : d277813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265936, d277813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265936, d277813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265937 q = 1) (hb : d277739 q = 1) : d277814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265937, d277814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265937, d277814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81716 (p : Pattern) (ha : d265943 p = 1) (hb : d277739 p = 1) : d277820 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d277739 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265921 q = 1) (hb : d277739 q = 1) : d277779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265921, d277779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81708 q ha hb
    | true =>
      simp only [d265921, d277779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81710 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d277739 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265922 q = 1) (hb : d277739 q = 1) : d277780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265922, d277780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265922, d277780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265923 q = 1) (hb : d277739 q = 1) : d277781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265923, d277781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265923, d277781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265924 q = 1) (hb : d277739 q = 1) : d277782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265924, d277782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265924, d277782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265928 q = 1) (hb : d277739 q = 1) : d277786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265928, d277786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265928, d277786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81711 q ha hb
  have h8 (q : Pattern) (ha : d265929 q = 1) (hb : d277739 q = 1) : d277787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265929, d277787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265929, d277787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d265930 q = 1) (hb : d277739 q = 1) : d277788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265930, d277788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265930, d277788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d265931 q = 1) (hb : d277739 q = 1) : d277789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265931, d277789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265931, d277789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265932 q = 1) (hb : d277739 q = 1) : d277790 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265932, d277790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265932, d277790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265938 q = 1) (hb : d277739 q = 1) : d277815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265938, d277815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265938, d277815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81715 q ha hb
  have h13 (q : Pattern) (ha : d265939 q = 1) (hb : d277739 q = 1) : d277816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265939, d277816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265939, d277816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d265940 q = 1) (hb : d277739 q = 1) : d277817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265940, d277817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265940, d277817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d265941 q = 1) (hb : d277739 q = 1) : d277818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265941, d277818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265941, d277818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d265942 q = 1) (hb : d277739 q = 1) : d277819 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265942, d277819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265942, d277819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265943 q = 1) (hb : d277739 q = 1) : d277820 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265943, d277820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265943, d277820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro81717 (p : Pattern) (ha : d33303 p = 1) (hb : d277739 p = 1) : d277830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277739 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d277739 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d277739 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d277739 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d277739 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d277739 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33303 q = 1) (hb : d277739 q = 1) : d277830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33303, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33303, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81718 (p : Pattern) (ha : d33310 p = 1) (hb : d277739 p = 1) : d277837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277739 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d277739 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d277739 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d277739 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d277739 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d277739 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d277739 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33246 q = 1) (hb : d277739 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81709 q ha hb
    | true =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33306 q = 1) (hb : d277739 q = 1) : d277833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33307 q = 1) (hb : d277739 q = 1) : d277834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33307, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33308 q = 1) (hb : d277739 q = 1) : d277835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33309 q = 1) (hb : d277739 q = 1) : d277836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33310 q = 1) (hb : d277739 q = 1) : d277837 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33310, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33310, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro81719 (p : Pattern) (ha : d33421 p = 1) (hb : d277739 p = 1) : d277918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277739 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33239 q = 1) (hb : d277739 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33299 q = 1) (hb : d277739 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33299, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33300 q = 1) (hb : d277739 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33300, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33301 q = 1) (hb : d277739 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33301, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33302 q = 1) (hb : d277739 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33302, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d277739 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33421 q = 1) (hb : d277739 q = 1) : d277918 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33421, d277918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33421, d277918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81720 (p : Pattern) (ha : d33315 p = 1) (hb : d277739 p = 1) : d277842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277739 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d277739 q = 1) : d277841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33315 q = 1) (hb : d277739 q = 1) : d277842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33315, d277842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33315, d277842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81721 (p : Pattern) (ha : d33322 p = 1) (hb : d277739 p = 1) : d277849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d277739 q = 1) : d277847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d277739 q = 1) : d277848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33322 q = 1) (hb : d277739 q = 1) : d277849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33322, d277849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33322, d277849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro81722 (p : Pattern) (ha : d33327 p = 1) (hb : d277739 p = 1) : d277853 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33326 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33326, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33326, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d33213 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33213, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33213, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d33327 q = 1) (hb : d277739 q = 1) : d277853 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d33327, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33327, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro81723 (p : Pattern) (ha : d33333 p = 1) (hb : d277739 p = 1) : d277859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33328 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33328, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81722 q ha hb
    | true =>
      simp only [d33328, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33329 q = 1) (hb : d277739 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33329, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33329, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33215 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81703 q ha hb
    | true =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33216 q = 1) (hb : d277739 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33330 q = 1) (hb : d277739 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33330, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33330, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d277739 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33217 q = 1) (hb : d277739 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33331 q = 1) (hb : d277739 q = 1) : d277857 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33331, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33331, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33332 q = 1) (hb : d277739 q = 1) : d277858 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33332, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33332, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d277739 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33218 q = 1) (hb : d277739 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33219 q = 1) (hb : d277739 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33333 q = 1) (hb : d277739 q = 1) : d277859 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33333, d277859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33333, d277859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro81724 (p : Pattern) (ha : d33341 p = 1) (hb : d277739 p = 1) : d277867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81703 q ha hb
    | true =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33216 q = 1) (hb : d277739 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d277739 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33217 q = 1) (hb : d277739 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33339 q = 1) (hb : d277739 q = 1) : d277865 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33339, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33339, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33340 q = 1) (hb : d277739 q = 1) : d277866 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33340, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33340, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d277739 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33341 q = 1) (hb : d277739 q = 1) : d277867 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33341, d277867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33341, d277867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81725 (p : Pattern) (ha : d33347 p = 1) (hb : d277739 p = 1) : d277873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33334 q = 1) (hb : d277739 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81723 q ha hb
    | true =>
      simp only [d33334, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33335 q = 1) (hb : d277739 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33335, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33336 q = 1) (hb : d277739 q = 1) : d277862 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33336, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33336, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33337 q = 1) (hb : d277739 q = 1) : d277863 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33337, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33337, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33221 q = 1) (hb : d277739 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33222 q = 1) (hb : d277739 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33223 q = 1) (hb : d277739 q = 1) : d277750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33224 q = 1) (hb : d277739 q = 1) : d277751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33338 q = 1) (hb : d277739 q = 1) : d277864 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33338, d277864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33338, d277864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33342 q = 1) (hb : d277739 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81724 q ha hb
    | true =>
      simp only [d33342, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33343 q = 1) (hb : d277739 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33343, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33344 q = 1) (hb : d277739 q = 1) : d277870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33344, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33344, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33345 q = 1) (hb : d277739 q = 1) : d277871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33345, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33345, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d277739 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d33346 q = 1) (hb : d277739 q = 1) : d277872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33346, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33346, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33347 q = 1) (hb : d277739 q = 1) : d277873 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33347, d277873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33347, d277873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro81726 (p : Pattern) (ha : d33353 p = 1) (hb : d277739 p = 1) : d277879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d277739 q = 1) : d277874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81725 q ha hb
    | true =>
      simp only [d33348, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d277739 q = 1) : d277875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d277739 q = 1) : d277876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d277739 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d277739 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
    | true =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d277739 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d277739 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d277739 q = 1) : d277877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d277739 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33230 q = 1) (hb : d277739 q = 1) : d277757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33352 q = 1) (hb : d277739 q = 1) : d277878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33352, d277878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33352, d277878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33353 q = 1) (hb : d277739 q = 1) : d277879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33353, d277879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33353, d277879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro81727 (p : Pattern) (ha : d33359 p = 1) (hb : d277739 p = 1) : d277885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d277739 q = 1) : d277880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81726 q ha hb
    | true =>
      simp only [d33354, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d277739 q = 1) : d277881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d277739 q = 1) : d277882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d277739 q = 1) : d277883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d277739 q = 1) : d277884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33359 q = 1) (hb : d277739 q = 1) : d277885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33359, d277885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33359, d277885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81728 (p : Pattern) (ha : d33392 p = 1) (hb : d277739 p = 1) : d277891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d277739 q = 1) : d277888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d277739 q = 1) : d277889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d277739 q = 1) : d277890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33392 q = 1) (hb : d277739 q = 1) : d277891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33392, d277891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33392, d277891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81729 (p : Pattern) (ha : d265953 p = 1) (hb : d277739 p = 1) : d277897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d277739 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d277739 q = 1) : d277843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81720 q ha hb
    | true =>
      simp only [d33316, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d277739 q = 1) : d277844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d277739 q = 1) : d277845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d277739 q = 1) : d277846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d277739 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d277739 q = 1) : d277850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81721 q ha hb
    | true =>
      simp only [d33323, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d277739 q = 1) : d277851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d277739 q = 1) : d277852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d277739 q = 1) : d277886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81727 q ha hb
    | true =>
      simp only [d33360, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d277739 q = 1) : d277887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d277739 q = 1) : d277892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81728 q ha hb
    | true =>
      simp only [d33393, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d277739 q = 1) : d277893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d277739 q = 1) : d277894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d277739 q = 1) : d277895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d277739 q = 1) : d277896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265953 q = 1) (hb : d277739 q = 1) : d277897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d277897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d277897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro81730 (p : Pattern) (ha : d33399 p = 1) (hb : d277739 p = 1) : d277898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277739 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33314 q = 1) (hb : d277739 q = 1) : d277841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33314, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33314, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33399 q = 1) (hb : d277739 q = 1) : d277898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33399, d277898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33399, d277898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro81731 (p : Pattern) (ha : d33404 p = 1) (hb : d277739 p = 1) : d277903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277739 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277739 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33320 q = 1) (hb : d277739 q = 1) : d277847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33320, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33320, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33321 q = 1) (hb : d277739 q = 1) : d277848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33321, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33321, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33404 q = 1) (hb : d277739 q = 1) : d277903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33404, d277903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33404, d277903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro81732 (p : Pattern) (ha : d33408 p = 1) (hb : d277739 p = 1) : d277907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33354 q = 1) (hb : d277739 q = 1) : d277880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33354, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81726 q ha hb
    | true =>
      simp only [d33354, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33355 q = 1) (hb : d277739 q = 1) : d277881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33355, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33355, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33356 q = 1) (hb : d277739 q = 1) : d277882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33356, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33356, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33357 q = 1) (hb : d277739 q = 1) : d277883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33357, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33357, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33358 q = 1) (hb : d277739 q = 1) : d277884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33358, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33358, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33408 q = 1) (hb : d277739 q = 1) : d277907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33408, d277907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33408, d277907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro81733 (p : Pattern) (ha : d33413 p = 1) (hb : d277739 p = 1) : d277910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277739 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81706 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277739 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33389 q = 1) (hb : d277739 q = 1) : d277888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33389, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33389, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33390 q = 1) (hb : d277739 q = 1) : d277889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33390, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33390, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33391 q = 1) (hb : d277739 q = 1) : d277890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33391, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33391, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33413 q = 1) (hb : d277739 q = 1) : d277910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33413, d277910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33413, d277910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81734 (p : Pattern) (ha : d265958 p = 1) (hb : d277739 p = 1) : d277916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d277739 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33316 q = 1) (hb : d277739 q = 1) : d277843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33316, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81720 q ha hb
    | true =>
      simp only [d33316, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33317 q = 1) (hb : d277739 q = 1) : d277844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33317, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33317, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33318 q = 1) (hb : d277739 q = 1) : d277845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33318, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33318, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33319 q = 1) (hb : d277739 q = 1) : d277846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33319, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33319, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d277739 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33323 q = 1) (hb : d277739 q = 1) : d277850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33323, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81721 q ha hb
    | true =>
      simp only [d33323, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33324 q = 1) (hb : d277739 q = 1) : d277851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33324, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33324, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33325 q = 1) (hb : d277739 q = 1) : d277852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33325, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33325, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33360 q = 1) (hb : d277739 q = 1) : d277886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33360, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81727 q ha hb
    | true =>
      simp only [d33360, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81707 q ha hb
  have h11 (q : Pattern) (ha : d265949 q = 1) (hb : d277739 q = 1) : d277887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265949, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d33393 q = 1) (hb : d277739 q = 1) : d277892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33393, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81728 q ha hb
    | true =>
      simp only [d33393, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33394 q = 1) (hb : d277739 q = 1) : d277893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33394, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33394, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d265950 q = 1) (hb : d277739 q = 1) : d277894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265950, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265951 q = 1) (hb : d277739 q = 1) : d277895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265951, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d265952 q = 1) (hb : d277739 q = 1) : d277896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265952, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d277739 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d33400 q = 1) (hb : d277739 q = 1) : d277899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33400, d277899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81730 q ha hb
    | true =>
      simp only [d33400, d277899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33401 q = 1) (hb : d277739 q = 1) : d277900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33401, d277900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33401, d277900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d33402 q = 1) (hb : d277739 q = 1) : d277901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33402, d277901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33402, d277901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d33403 q = 1) (hb : d277739 q = 1) : d277902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33403, d277902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33403, d277902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d277739 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d33405 q = 1) (hb : d277739 q = 1) : d277904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33405, d277904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81731 q ha hb
    | true =>
      simp only [d33405, d277904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d33406 q = 1) (hb : d277739 q = 1) : d277905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33406, d277905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33406, d277905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d33407 q = 1) (hb : d277739 q = 1) : d277906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33407, d277906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d33407, d277906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d33409 q = 1) (hb : d277739 q = 1) : d277908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81732 q ha hb
    | true =>
      simp only [d33409, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81709 q ha hb
  have h27 (q : Pattern) (ha : d265954 q = 1) (hb : d277739 q = 1) : d277909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d265954, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d33414 q = 1) (hb : d277739 q = 1) : d277911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81733 q ha hb
    | true =>
      simp only [d33414, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d33415 q = 1) (hb : d277739 q = 1) : d277912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d33415, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d265955 q = 1) (hb : d277739 q = 1) : d277913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d265955, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d265956 q = 1) (hb : d277739 q = 1) : d277914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d277914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d265956, d277914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d265957 q = 1) (hb : d277739 q = 1) : d277915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d277915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265957, d277915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d265958 q = 1) (hb : d277739 q = 1) : d277916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d277916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265958, d277916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro81735 (p : Pattern) (ha : d265965 p = 1) (hb : d277739 p = 1) : d277925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33409 q = 1) (hb : d277739 q = 1) : d277908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33409, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81732 q ha hb
    | true =>
      simp only [d33409, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81709 q ha hb
  have h2 (q : Pattern) (ha : d265954 q = 1) (hb : d277739 q = 1) : d277909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265954, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33414 q = 1) (hb : d277739 q = 1) : d277911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33414, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81733 q ha hb
    | true =>
      simp only [d33414, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33415 q = 1) (hb : d277739 q = 1) : d277912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33415, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33415, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d277739 q = 1) : d277913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265955, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d277739 q = 1) : d277923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d277923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d277923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d277739 q = 1) : d277924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d277924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d277924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d277739 q = 1) : d277925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d277925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d277925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81736 (p : Pattern) (ha : d33444 p = 1) (hb : d277739 p = 1) : d277941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33434 q = 1) (hb : d277739 q = 1) : d277931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33434, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33434, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81723 q ha hb
  have h2 (q : Pattern) (ha : d33334 q = 1) (hb : d277739 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33334, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81723 q ha hb
    | true =>
      simp only [d33334, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33435 q = 1) (hb : d277739 q = 1) : d277932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33435, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33435, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33335 q = 1) (hb : d277739 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33335, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33335, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33436 q = 1) (hb : d277739 q = 1) : d277933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33436, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33436, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33437 q = 1) (hb : d277739 q = 1) : d277934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33437, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33437, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33264 q = 1) (hb : d277739 q = 1) : d277791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
  have h8 (q : Pattern) (ha : d33221 q = 1) (hb : d277739 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81704 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33265 q = 1) (hb : d277739 q = 1) : d277792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33222 q = 1) (hb : d277739 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33266 q = 1) (hb : d277739 q = 1) : d277793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33267 q = 1) (hb : d277739 q = 1) : d277794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33438 q = 1) (hb : d277739 q = 1) : d277935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33438, d277935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33438, d277935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33439 q = 1) (hb : d277739 q = 1) : d277936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33439, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33439, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81724 q ha hb
  have h15 (q : Pattern) (ha : d33342 q = 1) (hb : d277739 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33342, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81724 q ha hb
    | true =>
      simp only [d33342, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33440 q = 1) (hb : d277739 q = 1) : d277937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33440, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33440, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d33343 q = 1) (hb : d277739 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33343, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33343, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33441 q = 1) (hb : d277739 q = 1) : d277938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33441, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33441, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33442 q = 1) (hb : d277739 q = 1) : d277939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33442, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33442, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d277739 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d33443 q = 1) (hb : d277739 q = 1) : d277940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33443, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33443, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d33444 q = 1) (hb : d277739 q = 1) : d277941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33444, d277941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33444, d277941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro81737 (p : Pattern) (ha : d33450 p = 1) (hb : d277739 p = 1) : d277947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33445 q = 1) (hb : d277739 q = 1) : d277942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33445, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81736 q ha hb
    | true =>
      simp only [d33445, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81712 q ha hb
  have h2 (q : Pattern) (ha : d33446 q = 1) (hb : d277739 q = 1) : d277943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33446, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33446, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33447 q = 1) (hb : d277739 q = 1) : d277944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33447, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33447, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d277739 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33270 q = 1) (hb : d277739 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33270, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81712 q ha hb
    | true =>
      simp only [d33270, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33271 q = 1) (hb : d277739 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33271, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33271, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33272 q = 1) (hb : d277739 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33272, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33272, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33448 q = 1) (hb : d277739 q = 1) : d277945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33448, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33448, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d277739 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33273 q = 1) (hb : d277739 q = 1) : d277800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33273, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33273, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33449 q = 1) (hb : d277739 q = 1) : d277946 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33449, d277946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33449, d277946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33450 q = 1) (hb : d277739 q = 1) : d277947 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33450, d277947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33450, d277947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro81738 (p : Pattern) (ha : d33456 p = 1) (hb : d277739 p = 1) : d277953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33451 q = 1) (hb : d277739 q = 1) : d277948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33451, d277948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81737 q ha hb
    | true =>
      simp only [d33451, d277948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33452 q = 1) (hb : d277739 q = 1) : d277949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33452, d277949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33452, d277949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33276 q = 1) (hb : d277739 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81713 q ha hb
    | true =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33277 q = 1) (hb : d277739 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33453 q = 1) (hb : d277739 q = 1) : d277950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33453, d277950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33453, d277950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33454 q = 1) (hb : d277739 q = 1) : d277951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33454, d277951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33454, d277951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33455 q = 1) (hb : d277739 q = 1) : d277952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33455, d277952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33455, d277952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33456 q = 1) (hb : d277739 q = 1) : d277953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33456, d277953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33456, d277953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro81739 (p : Pattern) (ha : d33481 p = 1) (hb : d277739 p = 1) : d277959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33276 q = 1) (hb : d277739 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81713 q ha hb
    | true =>
      simp only [d33276, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33277 q = 1) (hb : d277739 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33277, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33478 q = 1) (hb : d277739 q = 1) : d277956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33478, d277956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33478, d277956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33479 q = 1) (hb : d277739 q = 1) : d277957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33479, d277957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33479, d277957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33480 q = 1) (hb : d277739 q = 1) : d277958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33480, d277958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33480, d277958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33481 q = 1) (hb : d277739 q = 1) : d277959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33481, d277959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33481, d277959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro81740 (p : Pattern) (ha : d265975 p = 1) (hb : d277739 p = 1) : d277965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33457 q = 1) (hb : d277739 q = 1) : d277954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33457, d277954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81738 q ha hb
    | true =>
      simp only [d33457, d277954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81714 q ha hb
  have h2 (q : Pattern) (ha : d265971 q = 1) (hb : d277739 q = 1) : d277955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d277955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265971, d277955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33482 q = 1) (hb : d277739 q = 1) : d277960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33482, d277960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81739 q ha hb
    | true =>
      simp only [d33482, d277960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33483 q = 1) (hb : d277739 q = 1) : d277961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33483, d277961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33483, d277961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d277739 q = 1) : d277962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d277962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265972, d277962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d277739 q = 1) : d277963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d277963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d277963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d277739 q = 1) : d277964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d277964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d277964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d277739 q = 1) : d277965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d277965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d277965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81741 (p : Pattern) (ha : d265981 p = 1) (hb : d277739 p = 1) : d277971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33304 q = 1) (hb : d277739 q = 1) : d277831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33304, d277831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33304, d277831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81717 q ha hb
  have h2 (q : Pattern) (ha : d33305 q = 1) (hb : d277739 q = 1) : d277832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33305, d277832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33305, d277832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33311 q = 1) (hb : d277739 q = 1) : d277838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81717 q ha hb
    | true =>
      simp only [d33311, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81718 q ha hb
  have h4 (q : Pattern) (ha : d33312 q = 1) (hb : d277739 q = 1) : d277839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33312, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33313 q = 1) (hb : d277739 q = 1) : d277840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d33313, d277840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33313, d277840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265959 q = 1) (hb : d277739 q = 1) : d277917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d277917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81729 q ha hb
    | true =>
      simp only [d265959, d277917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81734 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d277739 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33422 q = 1) (hb : d277739 q = 1) : d277919 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33422, d277919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81719 q ha hb
    | true =>
      simp only [d33422, d277919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265960 q = 1) (hb : d277739 q = 1) : d277920 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d277920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265960, d277920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265961 q = 1) (hb : d277739 q = 1) : d277921 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d277921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265961, d277921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d265962 q = 1) (hb : d277739 q = 1) : d277922 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d277922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265962, d277922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265966 q = 1) (hb : d277739 q = 1) : d277926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d277926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265966, d277926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81735 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d277739 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d265967 q = 1) (hb : d277739 q = 1) : d277927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d277927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265967, d277927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d265968 q = 1) (hb : d277739 q = 1) : d277928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d277928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265968, d277928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d265969 q = 1) (hb : d277739 q = 1) : d277929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d277929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265969, d277929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d265970 q = 1) (hb : d277739 q = 1) : d277930 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d277930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265970, d277930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265976 q = 1) (hb : d277739 q = 1) : d277966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d277966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265976, d277966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81740 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d277739 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d265977 q = 1) (hb : d277739 q = 1) : d277967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d277967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d265977, d277967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d265978 q = 1) (hb : d277739 q = 1) : d277968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d277968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d265978, d277968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d265979 q = 1) (hb : d277739 q = 1) : d277969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d277969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d265979, d277969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d265980 q = 1) (hb : d277739 q = 1) : d277970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d277970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d265980, d277970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d265981 q = 1) (hb : d277739 q = 1) : d277971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d277971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265981, d277971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro81742 (p : Pattern) (ha : d265987 p = 1) (hb : d277739 p = 1) : d277977 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d277739 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d265944 q = 1) (hb : d277739 q = 1) : d277821 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265944, d277821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265944, d277821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81716 q ha hb
  have h3 (q : Pattern) (ha : d265945 q = 1) (hb : d277739 q = 1) : d277822 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265945, d277822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265945, d277822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d265946 q = 1) (hb : d277739 q = 1) : d277823 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265946, d277823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265946, d277823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265947 q = 1) (hb : d277739 q = 1) : d277824 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265947, d277824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265947, d277824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265948 q = 1) (hb : d277739 q = 1) : d277825 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265948, d277825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265948, d277825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d277739 q = 1) : d277972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d277972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d277972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81741 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d277739 q = 1) : d277973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d277973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d277973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d277739 q = 1) : d277974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d277974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d277974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d277739 q = 1) : d277975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d277975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d277975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d277739 q = 1) : d277976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d277976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d277976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d277739 q = 1) : d277977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d277977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265987, d277977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro81743 (p : Pattern) (ha : d33502 p = 1) (hb : d277739 p = 1) : d277980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33348 q = 1) (hb : d277739 q = 1) : d277874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33348, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81725 q ha hb
    | true =>
      simp only [d33348, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
  have h2 (q : Pattern) (ha : d33349 q = 1) (hb : d277739 q = 1) : d277875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33349, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33349, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33350 q = 1) (hb : d277739 q = 1) : d277876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33350, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33350, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d277739 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33227 q = 1) (hb : d277739 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
    | true =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33228 q = 1) (hb : d277739 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33229 q = 1) (hb : d277739 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33351 q = 1) (hb : d277739 q = 1) : d277877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33351, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33351, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33500 q = 1) (hb : d277739 q = 1) : d277978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33500, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d33501 q = 1) (hb : d277739 q = 1) : d277979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33501, d277979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33501, d277979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33502 q = 1) (hb : d277739 q = 1) : d277980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33502, d277980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33502, d277980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro81744 (p : Pattern) (ha : d33506 p = 1) (hb : d277739 p = 1) : d277984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d277739 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d277739 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81705 q ha hb
    | true =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d277739 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d277739 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33500 q = 1) (hb : d277739 q = 1) : d277978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33500, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33500, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33505 q = 1) (hb : d277739 q = 1) : d277983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33505, d277983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33505, d277983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33506 q = 1) (hb : d277739 q = 1) : d277984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33506, d277984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33506, d277984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro81745 (p : Pattern) (ha : d33512 p = 1) (hb : d277739 p = 1) : d277990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d277739 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81743 q ha hb
    | true =>
      simp only [d33503, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d277739 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d277739 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81744 q ha hb
    | true =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d277739 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d277739 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d277739 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d277739 q = 1) : d277989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33512 q = 1) (hb : d277739 q = 1) : d277990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33512, d277990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33512, d277990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro81746 (p : Pattern) (ha : d33516 p = 1) (hb : d277739 p = 1) : d277994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d277739 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81744 q ha hb
    | true =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d277739 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d277739 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d277739 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d277739 q = 1) : d277993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33516 q = 1) (hb : d277739 q = 1) : d277994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33516, d277994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33516, d277994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81747 (p : Pattern) (ha : d33522 p = 1) (hb : d277739 p = 1) : d278000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33517 q = 1) (hb : d277739 q = 1) : d277995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33517, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81745 q ha hb
    | true =>
      simp only [d33517, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81746 q ha hb
  have h2 (q : Pattern) (ha : d33518 q = 1) (hb : d277739 q = 1) : d277996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33518, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33518, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33519 q = 1) (hb : d277739 q = 1) : d277997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33519, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33519, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33520 q = 1) (hb : d277739 q = 1) : d277998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33520, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33520, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33521 q = 1) (hb : d277739 q = 1) : d277999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33521, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33521, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33522 q = 1) (hb : d277739 q = 1) : d278000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33522, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33522, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro81748 (p : Pattern) (ha : d33525 p = 1) (hb : d277739 p = 1) : d278003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33503 q = 1) (hb : d277739 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33503, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81743 q ha hb
    | true =>
      simp only [d33503, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33504 q = 1) (hb : d277739 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33504, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33504, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33507 q = 1) (hb : d277739 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81744 q ha hb
    | true =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33508 q = 1) (hb : d277739 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33509 q = 1) (hb : d277739 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33509, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33509, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33510 q = 1) (hb : d277739 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33510, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33510, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33511 q = 1) (hb : d277739 q = 1) : d277989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33511, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33511, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33525 q = 1) (hb : d277739 q = 1) : d278003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33525, d278003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33525, d278003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro81749 (p : Pattern) (ha : d33526 p = 1) (hb : d277739 p = 1) : d278004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33507 q = 1) (hb : d277739 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81744 q ha hb
    | true =>
      simp only [d33507, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33508 q = 1) (hb : d277739 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33508, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33513 q = 1) (hb : d277739 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33513, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33513, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33514 q = 1) (hb : d277739 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33514, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33514, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33515 q = 1) (hb : d277739 q = 1) : d277993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33515, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33515, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33526 q = 1) (hb : d277739 q = 1) : d278004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33526, d278004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33526, d278004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
