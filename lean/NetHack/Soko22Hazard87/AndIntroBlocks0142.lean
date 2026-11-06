import NetHack.Soko22Hazard87.AndIntroBlocks0141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro35500 (p : Pattern) (ha : d167285 p = 1) (hb : d168112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167280 q = 1) (hb : d168107 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167280, d168107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35499 q ha hb
    | true =>
      simp only [d167280, d168107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167281 q = 1) (hb : d168108 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167281, d168108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167281, d168108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136999 q = 1) (hb : d167991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35470 q ha hb
    | true =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137000 q = 1) (hb : d167992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167282 q = 1) (hb : d168109 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167282, d168109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167282, d168109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167283 q = 1) (hb : d168110 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167283, d168110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167283, d168110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167284 q = 1) (hb : d168111 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167284, d168111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167284, d168111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167285 q = 1) (hb : d168112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167285, d168112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167285, d168112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35501 (p : Pattern) (ha : d167291 p = 1) (hb : d168124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167286 q = 1) (hb : d168113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167286, d168113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35500 q ha hb
    | true =>
      simp only [d167286, d168113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35471 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167287 q = 1) (hb : d168114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167287, d168114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167287, d168114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137125 q = 1) (hb : d168119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137125, d168119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35496 q ha hb
    | true =>
      simp only [d137125, d168119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137126 q = 1) (hb : d168120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137126, d168120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137126, d168120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167288 q = 1) (hb : d168121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167288, d168121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167288, d168121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167289 q = 1) (hb : d168122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167289, d168122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167289, d168122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167290 q = 1) (hb : d168123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167290, d168123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167290, d168123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167291 q = 1) (hb : d168124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167291, d168124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167291, d168124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35502 (p : Pattern) (ha : d167297 p = 1) (hb : d168130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137028 q = 1) (hb : d168020 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137028, d168020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137028, d168020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35477 q ha hb
  have h2 (q : Pattern) (ha : d137029 q = 1) (hb : d168021 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137029, d168021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137029, d168021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137035 q = 1) (hb : d168027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137035, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35477 q ha hb
    | true =>
      simp only [d137035, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35478 q ha hb
  have h4 (q : Pattern) (ha : d137036 q = 1) (hb : d168028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137036, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137036, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137037 q = 1) (hb : d168029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137037, d168029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137037, d168029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167263 q = 1) (hb : d168086 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167263, d168086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35489 q ha hb
    | true =>
      simp only [d167263, d168086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35494 q ha hb
  have h7 (q : Pattern) (ha : d137094 q = 1) (hb : d168088 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137094, d168088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35479 q ha hb
    | true =>
      simp only [d137094, d168088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35455 q hb ha
  have h8 (q : Pattern) (ha : d167264 q = 1) (hb : d168089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167264, d168089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167264, d168089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167265 q = 1) (hb : d168090 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167265, d168090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167265, d168090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d167266 q = 1) (hb : d168091 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167266, d168091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167266, d168091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167270 q = 1) (hb : d168095 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167270, d168095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167270, d168095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35495 q ha hb
  have h12 (q : Pattern) (ha : d120335 q = 1) (hb : d137103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d137103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120335, d137103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35475 q ha hb
  have h13 (q : Pattern) (ha : d167271 q = 1) (hb : d168096 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167271, d168096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167271, d168096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d167272 q = 1) (hb : d168097 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167272, d168097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167272, d168097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167273 q = 1) (hb : d168098 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167273, d168098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d167273, d168098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d167274 q = 1) (hb : d168099 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167274, d168099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167274, d168099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167292 q = 1) (hb : d168125 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167292, d168125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167292, d168125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35501 q ha hb
  have h18 (q : Pattern) (ha : d120379 q = 1) (hb : d137137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d137137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120379, d137137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35476 q ha hb
  have h19 (q : Pattern) (ha : d167293 q = 1) (hb : d168126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167293, d168126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167293, d168126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d167294 q = 1) (hb : d168127 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167294, d168127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167294, d168127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d167295 q = 1) (hb : d168128 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167295, d168128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d167295, d168128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d167296 q = 1) (hb : d168129 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167296, d168129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167296, d168129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167297 q = 1) (hb : d168130 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167297, d168130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167297, d168130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35503 (p : Pattern) (ha : d167303 p = 1) (hb : d168136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167298 q = 1) (hb : d168131 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167298, d168131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167298, d168131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35502 q ha hb
  have h2 (q : Pattern) (ha : d167299 q = 1) (hb : d168132 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167299, d168132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167299, d168132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167300 q = 1) (hb : d168133 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167300, d168133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167300, d168133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167301 q = 1) (hb : d168134 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167301, d168134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167301, d168134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167302 q = 1) (hb : d168135 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167302, d168135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167302, d168135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167303 q = 1) (hb : d168136 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167303, d168136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167303, d168136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35504 (p : Pattern) (ha : d52434 p = 1) (hb : d120392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52434 q = 1) (hb : d120392 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35505 (p : Pattern) (ha : d120406 p = 1) (hb : d137161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52434 q = 1) (hb : d120397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35504 q ha hb
    | true =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d120398 q = 1) (hb : d137152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120399 q = 1) (hb : d137153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120400 q = 1) (hb : d137155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120400, d137155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120400, d137155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120405 q = 1) (hb : d137160 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120405, d137160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120405, d137160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120406 q = 1) (hb : d137161 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120406, d137161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120406, d137161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35506 (p : Pattern) (ha : d120416 p = 1) (hb : d137171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d137169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120415 q = 1) (hb : d137170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120415, d137170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120415, d137170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120416 q = 1) (hb : d137171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120416, d137171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120416, d137171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35507 (p : Pattern) (ha : d120426 p = 1) (hb : d137181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d137169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120415 q = 1) (hb : d137170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120415, d137170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120415, d137170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120426 q = 1) (hb : d137181 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120426, d137181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120426, d137181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35508 (p : Pattern) (ha : d120525 p = 1) (hb : d137271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120514 q = 1) (hb : d137260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120514, d137260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q ha hb
    | true =>
      simp only [d120514, d137260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120515 q = 1) (hb : d137261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120515, d137261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120515, d137261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120516 q = 1) (hb : d137262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120516, d137262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120516, d137262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120517 q = 1) (hb : d137263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120517, d137263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120517, d137263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120518 q = 1) (hb : d137264 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120518, d137264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120518, d137264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120520 q = 1) (hb : d137266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120520, d137266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35507 q ha hb
    | true =>
      simp only [d120520, d137266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120521 q = 1) (hb : d137267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120521, d137267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120521, d137267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120522 q = 1) (hb : d137268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120522, d137268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120522, d137268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120523 q = 1) (hb : d137269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120523, d137269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120523, d137269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120524 q = 1) (hb : d137270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120524, d137270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120524, d137270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120525 q = 1) (hb : d137271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120525, d137271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120525, d137271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35509 (p : Pattern) (ha : d120534 p = 1) (hb : d137280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120520 q = 1) (hb : d137266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120520, d137266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35507 q ha hb
    | true =>
      simp only [d120520, d137266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120521 q = 1) (hb : d137267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120521, d137267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120521, d137267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120522 q = 1) (hb : d137268 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120522, d137268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120522, d137268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120523 q = 1) (hb : d137269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120523, d137269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120523, d137269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120524 q = 1) (hb : d137270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120524, d137270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120524, d137270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120534 q = 1) (hb : d137280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120534, d137280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120534, d137280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35510 (p : Pattern) (ha : d52599 p = 1) (hb : d120545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h3 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d52599 q = 1) (hb : d120545 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35511 (p : Pattern) (ha : d120567 p = 1) (hb : d137308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52599 q = 1) (hb : d120562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35510 q ha hb
    | true =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d120563 q = 1) (hb : d137291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120564 q = 1) (hb : d137292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120565 q = 1) (hb : d137298 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120565, d137298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120565, d137298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120566 q = 1) (hb : d137307 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120566, d137307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120566, d137307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120567 q = 1) (hb : d137308 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120567, d137308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120567, d137308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35512 (p : Pattern) (ha : d120594 p = 1) (hb : d137319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120568 q = 1) (hb : d137309 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120568, d137309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35511 q ha hb
    | true =>
      simp only [d120568, d137309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120569 q = 1) (hb : d137310 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120569, d137310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120569, d137310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120591 q = 1) (hb : d137316 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120591, d137316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120591, d137316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120592 q = 1) (hb : d137317 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120592, d137317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120592, d137317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120593 q = 1) (hb : d137318 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120593, d137318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120593, d137318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120594 q = 1) (hb : d137319 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120594, d137319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120594, d137319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35513 (p : Pattern) (ha : d120600 p = 1) (hb : d137345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120595 q = 1) (hb : d137340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120595, d137340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35512 q ha hb
    | true =>
      simp only [d120595, d137340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120596 q = 1) (hb : d137341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120596, d137341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120596, d137341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120597 q = 1) (hb : d137342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120597, d137342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120597, d137342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120598 q = 1) (hb : d137343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120598, d137343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120598, d137343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120599 q = 1) (hb : d137344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120599, d137344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120599, d137344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120600 q = 1) (hb : d137345 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120600, d137345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120600, d137345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35514 (p : Pattern) (ha : d52432 p = 1) (hb : d168042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
    | true =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9470 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12748 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12748, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12749 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12749, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14262 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14262, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52432 q = 1) (hb : d168042 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35515 (p : Pattern) (ha : d137157 p = 1) (hb : d168140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52432 q = 1) (hb : d168043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35514 q ha hb
    | true =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137150 q = 1) (hb : d168044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137150, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137150, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137151 q = 1) (hb : d168045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137151, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137151, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52434 q = 1) (hb : d120397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35504 q ha hb
    | true =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d120398 q = 1) (hb : d137152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d120399 q = 1) (hb : d137153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137154 q = 1) (hb : d168138 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137154, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137154, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d120400 q = 1) (hb : d137155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120400, d137155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120400, d137155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d137156 q = 1) (hb : d168139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137156, d168139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137156, d168139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137157 q = 1) (hb : d168140 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137157, d168140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137157, d168140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35516 (p : Pattern) (ha : d137167 p = 1) (hb : d168146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d168144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137166 q = 1) (hb : d168145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137166, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137166, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137167 q = 1) (hb : d168146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137167, d168146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137167, d168146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35517 (p : Pattern) (ha : d137177 p = 1) (hb : d168152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
    | true =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q hb ha
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d168148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d168149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d168150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d168151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137177 q = 1) (hb : d168152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137177, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137177, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35518 (p : Pattern) (ha : d137180 p = 1) (hb : d168155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d168144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137166 q = 1) (hb : d168145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137166, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137166, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137180 q = 1) (hb : d168155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137180, d168155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137180, d168155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35519 (p : Pattern) (ha : d137187 p = 1) (hb : d168161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
    | true =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q hb ha
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d168148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d168149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d168150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d168151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137182 q = 1) (hb : d168156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35518 q ha hb
    | true =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35507 q hb ha
  have h7 (q : Pattern) (ha : d137183 q = 1) (hb : d168157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137183, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137183, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137184 q = 1) (hb : d168158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137184, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137184, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137185 q = 1) (hb : d168159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137185, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137185, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137186 q = 1) (hb : d168160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137186, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137186, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137187 q = 1) (hb : d168161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137187, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137187, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35520 (p : Pattern) (ha : d137265 p = 1) (hb : d168222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137172 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
    | true =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q hb ha
  have h2 (q : Pattern) (ha : d137173 q = 1) (hb : d168148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137173, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137174 q = 1) (hb : d168149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137174, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137175 q = 1) (hb : d168150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137175, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137176 q = 1) (hb : d168151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137176, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120514 q = 1) (hb : d137260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120514, d137260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q ha hb
    | true =>
      simp only [d120514, d137260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120515 q = 1) (hb : d137261 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120515, d137261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120515, d137261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120516 q = 1) (hb : d137262 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120516, d137262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120516, d137262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120517 q = 1) (hb : d137263 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120517, d137263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120517, d137263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120518 q = 1) (hb : d137264 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120518, d137264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120518, d137264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137265 q = 1) (hb : d168222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137265, d168222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137265, d168222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro35521 (p : Pattern) (ha : d120439 p = 1) (hb : d137194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d137169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120438 q = 1) (hb : d137193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120438, d137193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120438, d137193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120439 q = 1) (hb : d137194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120439, d137194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120439, d137194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35522 (p : Pattern) (ha : d120449 p = 1) (hb : d137204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120447 q = 1) (hb : d137202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120447, d137202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120447, d137202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120448 q = 1) (hb : d137203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120448, d137203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120448, d137203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120449 q = 1) (hb : d137204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120449, d137204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120449, d137204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35523 (p : Pattern) (ha : d137192 p = 1) (hb : d168166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d168144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137191 q = 1) (hb : d168165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137191, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137191, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137192 q = 1) (hb : d168166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137192, d168166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137192, d168166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35524 (p : Pattern) (ha : d137201 p = 1) (hb : d168173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137199 q = 1) (hb : d168171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137199, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137199, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137200 q = 1) (hb : d168172 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137200, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137200, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137201 q = 1) (hb : d168173 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137201, d168173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137201, d168173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35525 (p : Pattern) (ha : d9580 p = 1) (hb : d52111 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309 q = 1) (hb : d52108 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51980 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d825 q = 1) (hb : d52109 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d52109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d825, d52109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51981 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5121 q = 1) (hb : d52110 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5121, d52110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5121, d52110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1519 q = 1) (hb : d51980 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1519, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1531 q = 1) (hb : d51981 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1531, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d16 q = 1) (hb : d51868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9579 q = 1) (hb : d51982 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9579, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9580 q = 1) (hb : d52111 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9580, d52111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9580, d52111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35526 (p : Pattern) (ha : d9596 p = 1) (hb : d52289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d52278 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9581 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9581, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9582, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9593 q = 1) (hb : d52280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9593, d52280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9594 q = 1) (hb : d52287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9594, d52287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9595 q = 1) (hb : d52288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9595, d52288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9452 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9453 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9583 q = 1) (hb : d52114 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9583, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9584 q = 1) (hb : d52115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9584, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9585 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9585, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9596 q = 1) (hb : d52289 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9596, d52289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9596, d52289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35527 (p : Pattern) (ha : d52294 p = 1) (hb : d168177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9597 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35526 q ha hb
    | true =>
      simp only [d9597, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9599 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9599, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14529 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14529, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14530 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14530, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14531 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14531, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14531, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52294 q = 1) (hb : d168177 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35528 (p : Pattern) (ha : d113136 p = 1) (hb : d168042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12748 q = 1) (hb : d113134 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12749 q = 1) (hb : d113135 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14262 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14262, d113136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113136 q = 1) (hb : d168042 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35529 (p : Pattern) (ha : d167309 p = 1) (hb : d168183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52294 q = 1) (hb : d168178 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35527 q ha hb
    | true =>
      simp only [d168178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137208 q = 1) (hb : d168179 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137208, d168179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137208, d168179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137209 q = 1) (hb : d168180 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137209, d168180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137209, d168180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113136 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113136 q = 1) (hb : d168043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35528 q ha hb
    | true =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167305 q = 1) (hb : d168044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167305, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167305, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167306 q = 1) (hb : d168045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167306, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167306, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167307 q = 1) (hb : d168181 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167307, d168181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167307, d168181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52432 q = 1) (hb : d168043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35514 q ha hb
    | true =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137150 q = 1) (hb : d168044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137150, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137150, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137151 q = 1) (hb : d168045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137151, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137151, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52434 q = 1) (hb : d120397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35504 q ha hb
    | true =>
      simp only [d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d120398 q = 1) (hb : d137152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120398, d137152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d120399 q = 1) (hb : d137153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120399, d137153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137154 q = 1) (hb : d168138 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137154, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137154, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d167308 q = 1) (hb : d168182 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167308, d168182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167308, d168182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167309 q = 1) (hb : d168183 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167309, d168183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167309, d168183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35530 (p : Pattern) (ha : d167315 p = 1) (hb : d168189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167310 q = 1) (hb : d168184 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167310, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35529 q ha hb
    | true =>
      simp only [d167310, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167311 q = 1) (hb : d168185 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167311, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167311, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167312 q = 1) (hb : d168186 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167312, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167312, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167313 q = 1) (hb : d168187 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167313, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167313, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167314 q = 1) (hb : d168188 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167314, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167314, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167315 q = 1) (hb : d168189 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167315, d168189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167315, d168189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35531 (p : Pattern) (ha : d167321 p = 1) (hb : d168195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167318 q = 1) (hb : d168192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167318, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167318, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167319 q = 1) (hb : d168193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167319, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167319, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167320 q = 1) (hb : d168194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167320, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167320, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167321 q = 1) (hb : d168195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167321, d168195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167321, d168195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35532 (p : Pattern) (ha : d167327 p = 1) (hb : d168201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137195 q = 1) (hb : d168167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137195, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35523 q ha hb
    | true =>
      simp only [d137195, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35521 q hb ha
  have h2 (q : Pattern) (ha : d137196 q = 1) (hb : d168168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137196, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137196, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137197 q = 1) (hb : d168169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137197, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137197, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137198 q = 1) (hb : d168170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137198, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137198, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137205 q = 1) (hb : d168174 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137205, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35524 q ha hb
    | true =>
      simp only [d137205, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35522 q hb ha
  have h6 (q : Pattern) (ha : d137206 q = 1) (hb : d168175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137206, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137206, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137207 q = 1) (hb : d168176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137207, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137207, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167316 q = 1) (hb : d168190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167316, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35530 q ha hb
    | true =>
      simp only [d167316, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167317 q = 1) (hb : d168191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167317, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167317, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167322 q = 1) (hb : d168196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167322, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35531 q ha hb
    | true =>
      simp only [d167322, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167323 q = 1) (hb : d168197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167323, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167323, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167324 q = 1) (hb : d168198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167324, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167324, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167325 q = 1) (hb : d168199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167325, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167325, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167326 q = 1) (hb : d168200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167326, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167326, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167327 q = 1) (hb : d168201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167327, d168201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167327, d168201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35533 (p : Pattern) (ha : d120487 p = 1) (hb : d137239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120414 q = 1) (hb : d137169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120414, d137169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120438 q = 1) (hb : d137193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120438, d137193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120438, d137193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120487 q = 1) (hb : d137239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120487, d137239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120487, d137239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35534 (p : Pattern) (ha : d120493 p = 1) (hb : d137245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120413 q = 1) (hb : d137168 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120413, d137168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120447 q = 1) (hb : d137202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120447, d137202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120447, d137202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120448 q = 1) (hb : d137203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120448, d137203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120448, d137203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120493 q = 1) (hb : d137245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120493, d137245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120493, d137245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35535 (p : Pattern) (ha : d137238 p = 1) (hb : d168202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137165 q = 1) (hb : d168144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137165, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137191 q = 1) (hb : d168165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137191, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137191, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137238 q = 1) (hb : d168202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137238, d168202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137238, d168202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35536 (p : Pattern) (ha : d137244 p = 1) (hb : d168207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120407 q = 1) (hb : d137162 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35505 q ha hb
    | true =>
      simp only [d120407, d137162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120408 q = 1) (hb : d137163 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120408, d137163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137164 q = 1) (hb : d168143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137164, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137199 q = 1) (hb : d168171 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137199, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137199, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137200 q = 1) (hb : d168172 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137200, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137200, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137244 q = 1) (hb : d168207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137244, d168207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137244, d168207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35537 (p : Pattern) (ha : d167328 p = 1) (hb : d168211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167310 q = 1) (hb : d168184 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167310, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35529 q ha hb
    | true =>
      simp only [d167310, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167311 q = 1) (hb : d168185 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167311, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167311, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167312 q = 1) (hb : d168186 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167312, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167312, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167313 q = 1) (hb : d168187 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167313, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167313, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167314 q = 1) (hb : d168188 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167314, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167314, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167328 q = 1) (hb : d168211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167328, d168211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167328, d168211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35538 (p : Pattern) (ha : d167331 p = 1) (hb : d168214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137158 q = 1) (hb : d168141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35515 q ha hb
    | true =>
      simp only [d137158, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137159 q = 1) (hb : d168142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137159, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167318 q = 1) (hb : d168192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167318, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167318, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167319 q = 1) (hb : d168193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167319, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167319, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167320 q = 1) (hb : d168194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167320, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167320, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167331 q = 1) (hb : d168214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167331, d168214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167331, d168214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35539 (p : Pattern) (ha : d167337 p = 1) (hb : d168220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137195 q = 1) (hb : d168167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137195, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35523 q ha hb
    | true =>
      simp only [d137195, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35521 q hb ha
  have h2 (q : Pattern) (ha : d137196 q = 1) (hb : d168168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137196, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137196, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137197 q = 1) (hb : d168169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137197, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137197, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137198 q = 1) (hb : d168170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137198, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137198, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137205 q = 1) (hb : d168174 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137205, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35524 q ha hb
    | true =>
      simp only [d137205, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35522 q hb ha
  have h6 (q : Pattern) (ha : d137206 q = 1) (hb : d168175 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137206, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137206, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137207 q = 1) (hb : d168176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137207, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137207, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167316 q = 1) (hb : d168190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167316, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35530 q ha hb
    | true =>
      simp only [d167316, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167317 q = 1) (hb : d168191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167317, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167317, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167322 q = 1) (hb : d168196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167322, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35531 q ha hb
    | true =>
      simp only [d167322, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167323 q = 1) (hb : d168197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167323, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167323, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167324 q = 1) (hb : d168198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167324, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167324, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167325 q = 1) (hb : d168199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167325, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167325, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167326 q = 1) (hb : d168200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167326, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167326, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137240 q = 1) (hb : d168203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137240, d168203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35535 q ha hb
    | true =>
      simp only [d137240, d168203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35533 q hb ha
  have h17 (q : Pattern) (ha : d137241 q = 1) (hb : d168204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137241, d168204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137241, d168204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137242 q = 1) (hb : d168205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137242, d168205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137242, d168205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137243 q = 1) (hb : d168206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137243, d168206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137243, d168206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137246 q = 1) (hb : d168208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137246, d168208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35536 q ha hb
    | true =>
      simp only [d137246, d168208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35534 q hb ha
  have h21 (q : Pattern) (ha : d137247 q = 1) (hb : d168209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137247, d168209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137247, d168209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137248 q = 1) (hb : d168210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137248, d168210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137248, d168210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167329 q = 1) (hb : d168212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167329, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35537 q ha hb
    | true =>
      simp only [d167329, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35518 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d137182 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d167330 q = 1) (hb : d168213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167330, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d167330, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d167332 q = 1) (hb : d168215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167332, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35538 q ha hb
    | true =>
      simp only [d167332, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d167333 q = 1) (hb : d168216 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167333, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d167333, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d167334 q = 1) (hb : d168217 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167334, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d167334, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d167335 q = 1) (hb : d168218 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167335, d168218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d167335, d168218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d167336 q = 1) (hb : d168219 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167336, d168219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167336, d168219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d167337 q = 1) (hb : d168220 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167337, d168220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167337, d168220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35540 (p : Pattern) (ha : d167344 p = 1) (hb : d168229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167329 q = 1) (hb : d168212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167329, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35537 q ha hb
    | true =>
      simp only [d167329, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35518 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137182 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167330 q = 1) (hb : d168213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167330, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167330, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167332 q = 1) (hb : d168215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167332, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35538 q ha hb
    | true =>
      simp only [d167332, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167333 q = 1) (hb : d168216 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167333, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167333, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167334 q = 1) (hb : d168217 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167334, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167334, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167342 q = 1) (hb : d168227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167342, d168227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167342, d168227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167343 q = 1) (hb : d168228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167343, d168228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167343, d168228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167344 q = 1) (hb : d168229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167344, d168229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167344, d168229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35541 (p : Pattern) (ha : d52594 p = 1) (hb : d168100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12858 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12858, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
  have h3 (q : Pattern) (ha : d9468 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
    | true =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12859 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12859, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9470 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12860 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12860, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12861 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12861, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14371 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14371, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52594 q = 1) (hb : d168100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35542 (p : Pattern) (ha : d137300 p = 1) (hb : d168246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52594 q = 1) (hb : d168101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35541 q ha hb
    | true =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137288 q = 1) (hb : d168102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137288, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137288, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137289 q = 1) (hb : d168103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137289, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137289, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d52599 q = 1) (hb : d120562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35510 q ha hb
    | true =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d120563 q = 1) (hb : d137291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d120564 q = 1) (hb : d137292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137293 q = 1) (hb : d168240 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137293, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137293, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d120565 q = 1) (hb : d137298 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120565, d137298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120565, d137298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d137299 q = 1) (hb : d168245 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137299, d168245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137299, d168245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137300 q = 1) (hb : d168246 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137300, d168246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137300, d168246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35543 (p : Pattern) (ha : d137314 p = 1) (hb : d168256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137301 q = 1) (hb : d168247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35542 q ha hb
    | true =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137302 q = 1) (hb : d168248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120568 q = 1) (hb : d137309 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120568, d137309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35511 q ha hb
    | true =>
      simp only [d120568, d137309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120569 q = 1) (hb : d137310 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120569, d137310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120569, d137310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137311 q = 1) (hb : d168253 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137311, d168253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137311, d168253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137312 q = 1) (hb : d168254 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137312, d168254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137312, d168254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137313 q = 1) (hb : d168255 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137313, d168255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137313, d168255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137314 q = 1) (hb : d168256 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137314, d168256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137314, d168256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35544 (p : Pattern) (ha : d52367 p = 1) (hb : d168235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14644 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14644, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35526 q ha hb
  have h3 (q : Pattern) (ha : d9597 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35526 q ha hb
    | true =>
      simp only [d9597, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14645 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14645, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9599 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9599, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14646 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14646, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14647 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14647, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14648 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14648, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14648, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52367 q = 1) (hb : d168235 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35545 (p : Pattern) (ha : d113218 p = 1) (hb : d168100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h3 (q : Pattern) (ha : d9468 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12859 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9470 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12860 q = 1) (hb : d113216 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12861 q = 1) (hb : d113217 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14371 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14371, d113218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113218 q = 1) (hb : d168100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35546 (p : Pattern) (ha : d167354 p = 1) (hb : d168242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52367 q = 1) (hb : d168236 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35544 q ha hb
    | true =>
      simp only [d168236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137286 q = 1) (hb : d168237 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137286, d168237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137286, d168237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137287 q = 1) (hb : d168238 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137287, d168238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137287, d168238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113218 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113218 q = 1) (hb : d168101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35545 q ha hb
    | true =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167350 q = 1) (hb : d168102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167350, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167350, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167351 q = 1) (hb : d168103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167351, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167351, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167352 q = 1) (hb : d168239 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167352, d168239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167352, d168239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52594 q = 1) (hb : d168101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35541 q ha hb
    | true =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137288 q = 1) (hb : d168102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137288, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137288, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137289 q = 1) (hb : d168103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137289, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137289, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d52599 q = 1) (hb : d120562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35510 q ha hb
    | true =>
      simp only [d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d120563 q = 1) (hb : d137291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120563, d137291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d120564 q = 1) (hb : d137292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120564, d137292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137293 q = 1) (hb : d168240 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137293, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137293, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d167353 q = 1) (hb : d168241 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167353, d168241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167353, d168241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167354 q = 1) (hb : d168242 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167354, d168242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167354, d168242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35547 (p : Pattern) (ha : d167360 p = 1) (hb : d168252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167355 q = 1) (hb : d168243 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167355, d168243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35546 q ha hb
    | true =>
      simp only [d167355, d168243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167356 q = 1) (hb : d168244 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167356, d168244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167356, d168244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137301 q = 1) (hb : d168247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35542 q ha hb
    | true =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137302 q = 1) (hb : d168248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167357 q = 1) (hb : d168249 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167357, d168249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167357, d168249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167358 q = 1) (hb : d168250 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167358, d168250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167358, d168250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167359 q = 1) (hb : d168251 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167359, d168251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167359, d168251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167360 q = 1) (hb : d168252 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167360, d168252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167360, d168252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35548 (p : Pattern) (ha : d167366 p = 1) (hb : d168262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137301 q = 1) (hb : d168247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35542 q ha hb
    | true =>
      simp only [d137301, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137302 q = 1) (hb : d168248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137302, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167363 q = 1) (hb : d168259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167363, d168259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167363, d168259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167364 q = 1) (hb : d168260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167364, d168260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167364, d168260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167365 q = 1) (hb : d168261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167365, d168261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167365, d168261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167366 q = 1) (hb : d168262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167366, d168262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167366, d168262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35549 (p : Pattern) (ha : d167372 p = 1) (hb : d168268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167361 q = 1) (hb : d168257 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167361, d168257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35547 q ha hb
    | true =>
      simp only [d167361, d168257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35543 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167362 q = 1) (hb : d168258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167362, d168258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167362, d168258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167367 q = 1) (hb : d168263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167367, d168263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35548 q ha hb
    | true =>
      simp only [d167367, d168263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167368 q = 1) (hb : d168264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167368, d168264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167368, d168264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167369 q = 1) (hb : d168265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167369, d168265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167369, d168265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167370 q = 1) (hb : d168266 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167370, d168266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167370, d168266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167371 q = 1) (hb : d168267 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167371, d168267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167371, d168267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167372 q = 1) (hb : d168268 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167372, d168268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167372, d168268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35550 (p : Pattern) (ha : d167378 p = 1) (hb : d168274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137178 q = 1) (hb : d168153 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137178, d168153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137178, d168153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35517 q ha hb
  have h2 (q : Pattern) (ha : d137179 q = 1) (hb : d168154 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137179, d168154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137179, d168154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137188 q = 1) (hb : d168162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137188, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35517 q ha hb
    | true =>
      simp only [d137188, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35519 q ha hb
  have h4 (q : Pattern) (ha : d137189 q = 1) (hb : d168163 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137189, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137189, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137190 q = 1) (hb : d168164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137190, d168164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137190, d168164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167338 q = 1) (hb : d168221 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167338, d168221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35532 q ha hb
    | true =>
      simp only [d167338, d168221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35539 q ha hb
  have h7 (q : Pattern) (ha : d137272 q = 1) (hb : d168223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137272, d168223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35520 q ha hb
    | true =>
      simp only [d137272, d168223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35508 q hb ha
  have h8 (q : Pattern) (ha : d167339 q = 1) (hb : d168224 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167339, d168224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167339, d168224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167340 q = 1) (hb : d168225 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167340, d168225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167340, d168225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d167341 q = 1) (hb : d168226 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167341, d168226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167341, d168226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167345 q = 1) (hb : d168230 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167345, d168230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167345, d168230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35540 q ha hb
  have h12 (q : Pattern) (ha : d120535 q = 1) (hb : d137281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120535, d137281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120535, d137281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35509 q ha hb
  have h13 (q : Pattern) (ha : d167346 q = 1) (hb : d168231 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167346, d168231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167346, d168231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d167347 q = 1) (hb : d168232 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167347, d168232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167347, d168232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167348 q = 1) (hb : d168233 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167348, d168233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d167348, d168233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d167349 q = 1) (hb : d168234 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167349, d168234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167349, d168234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167373 q = 1) (hb : d168269 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167373, d168269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167373, d168269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35549 q ha hb
  have h18 (q : Pattern) (ha : d120601 q = 1) (hb : d137346 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120601, d137346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120601, d137346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35513 q ha hb
  have h19 (q : Pattern) (ha : d167374 q = 1) (hb : d168270 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167374, d168270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167374, d168270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d167375 q = 1) (hb : d168271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167375, d168271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167375, d168271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d167376 q = 1) (hb : d168272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167376, d168272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d167376, d168272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d167377 q = 1) (hb : d168273 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167377, d168273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167377, d168273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167378 q = 1) (hb : d168274 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167378, d168274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167378, d168274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35551 (p : Pattern) (ha : d167384 p = 1) (hb : d168280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167379 q = 1) (hb : d168275 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167379, d168275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167379, d168275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35550 q ha hb
  have h2 (q : Pattern) (ha : d167380 q = 1) (hb : d168276 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167380, d168276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167380, d168276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167381 q = 1) (hb : d168277 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167381, d168277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167381, d168277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167382 q = 1) (hb : d168278 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167382, d168278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167382, d168278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167383 q = 1) (hb : d168279 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167383, d168279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167383, d168279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167384 q = 1) (hb : d168280 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167384, d168280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167384, d168280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35552 (p : Pattern) (ha : d9799 p = 1) (hb : d52701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9452 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9453 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9795 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9795, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9797 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9797, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9798 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9798, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h14 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d9799 q = 1) (hb : d52701 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9799, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9799, d52701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro35553 (p : Pattern) (ha : d52708 p = 1) (hb : d168287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9800 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35552 q ha hb
    | true =>
      simp only [d9800, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9802 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9802, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14763 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14763, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14764 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14764, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14765 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14765, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d52708 q = 1) (hb : d168287 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35554 (p : Pattern) (ha : d137371 p = 1) (hb : d168298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52708 q = 1) (hb : d168288 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35553 q ha hb
    | true =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137362 q = 1) (hb : d168289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137363 q = 1) (hb : d168290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137365 q = 1) (hb : d168292 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137365, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137365, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137370 q = 1) (hb : d168297 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137370, d168297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137370, d168297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137371 q = 1) (hb : d168298 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137371, d168298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137371, d168298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35555 (p : Pattern) (ha : d137381 p = 1) (hb : d168308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d168306 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137380 q = 1) (hb : d168307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137380, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137380, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137381 q = 1) (hb : d168308 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137381, d168308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137381, d168308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35556 (p : Pattern) (ha : d137391 p = 1) (hb : d168318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d168306 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137380 q = 1) (hb : d168307 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137380, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137380, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137391 q = 1) (hb : d168318 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137391, d168318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137391, d168318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35557 (p : Pattern) (ha : d137481 p = 1) (hb : d168403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137470 q = 1) (hb : d168392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137470, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
    | true =>
      simp only [d137470, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137471 q = 1) (hb : d168393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137471, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137471, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137472 q = 1) (hb : d168394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137472, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137472, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137473 q = 1) (hb : d168395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137473, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137473, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137474 q = 1) (hb : d168396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137474, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137474, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137476 q = 1) (hb : d168398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137476, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35556 q ha hb
    | true =>
      simp only [d137476, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137477 q = 1) (hb : d168399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137477, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137477, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137478 q = 1) (hb : d168400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137478, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137478, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137479 q = 1) (hb : d168401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137479, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137479, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137480 q = 1) (hb : d168402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137480, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137480, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137481 q = 1) (hb : d168403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137481, d168403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137481, d168403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35558 (p : Pattern) (ha : d137490 p = 1) (hb : d168412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137476 q = 1) (hb : d168398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137476, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35556 q ha hb
    | true =>
      simp only [d137476, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137477 q = 1) (hb : d168399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137477, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137477, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137478 q = 1) (hb : d168400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137478, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137478, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137479 q = 1) (hb : d168401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137479, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137479, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137480 q = 1) (hb : d168402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137480, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137480, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137490 q = 1) (hb : d168412 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137490, d168412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137490, d168412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35559 (p : Pattern) (ha : d52888 p = 1) (hb : d168427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15004 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15004, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35552 q ha hb
  have h3 (q : Pattern) (ha : d9800 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35552 q ha hb
    | true =>
      simp only [d9800, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15005 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15005, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9802 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9802, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15006 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15006, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15007 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15007, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15008 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15008, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d52888 q = 1) (hb : d168427 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35560 (p : Pattern) (ha : d137518 p = 1) (hb : d168446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52888 q = 1) (hb : d168428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35559 q ha hb
    | true =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137501 q = 1) (hb : d168429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137502 q = 1) (hb : d168430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137508 q = 1) (hb : d168436 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137508, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137508, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137517 q = 1) (hb : d168445 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137517, d168445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137517, d168445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137518 q = 1) (hb : d168446 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137518, d168446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137518, d168446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35561 (p : Pattern) (ha : d137529 p = 1) (hb : d168469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137519 q = 1) (hb : d168447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35560 q ha hb
    | true =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137520 q = 1) (hb : d168448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137526 q = 1) (hb : d168466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137526, d168466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137526, d168466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137527 q = 1) (hb : d168467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137527, d168467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137527, d168467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137528 q = 1) (hb : d168468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137528, d168468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137528, d168468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137529 q = 1) (hb : d168469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137529, d168469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137529, d168469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35562 (p : Pattern) (ha : d137555 p = 1) (hb : d168475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137550 q = 1) (hb : d168470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137550, d168470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35561 q ha hb
    | true =>
      simp only [d137550, d168470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137551 q = 1) (hb : d168471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137551, d168471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137551, d168471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137552 q = 1) (hb : d168472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137552, d168472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137552, d168472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137553 q = 1) (hb : d168473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137553, d168473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137553, d168473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137554 q = 1) (hb : d168474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137554, d168474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137554, d168474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137555 q = 1) (hb : d168475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137555, d168475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137555, d168475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35563 (p : Pattern) (ha : d9771 p = 1) (hb : d52674 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d52665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1085 q = 1) (hb : d52666 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, d52666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1085, d52666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1086 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, d52667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1086, d52667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51869 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9771 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9771, d52674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9771, d52674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro35564 (p : Pattern) (ha : d9777 p = 1) (hb : d52690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9581 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9582 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9768 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9768, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9769 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9769, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9770 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9770, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9772 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9772, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35563 q ha hb
  have h11 (q : Pattern) (ha : d9773 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9773, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9452 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9453 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9453, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9774 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9774, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d9775 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9775, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9776 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9776, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d9777 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9777, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9777, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35565 (p : Pattern) (ha : d52706 p = 1) (hb : d168283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9778 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35564 q ha hb
    | true =>
      simp only [d9778, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9780 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9780, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14758 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14758, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14759 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14759, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14760 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14760, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14760, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52706 q = 1) (hb : d168283 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35566 (p : Pattern) (ha : d9799 p = 1) (hb : d69107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9452 q = 1) (hb : d69102 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9453 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9453, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9795 q = 1) (hb : d69104 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9795, d69104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9797 q = 1) (hb : d69105 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9797, d69105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9798 q = 1) (hb : d69106 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9798, d69106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h14 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1117 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1117, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d1118 q = 1) (hb : d52699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1118, d52699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1119 q = 1) (hb : d52700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1119, d52700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d9799 q = 1) (hb : d69107 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9799, d69107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9799, d69107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro35567 (p : Pattern) (ha : d69112 p = 1) (hb : d168287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9800 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35566 q ha hb
    | true =>
      simp only [d9800, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9802 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9802, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14763 q = 1) (hb : d69110 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14763, d69110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14764 q = 1) (hb : d69111 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14764, d69111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14765 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14765, d69112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69112 q = 1) (hb : d168287 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35568 (p : Pattern) (ha : d167391 p = 1) (hb : d168294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52706 q = 1) (hb : d168284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35565 q ha hb
    | true =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137360 q = 1) (hb : d168285 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137361 q = 1) (hb : d168286 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69112 q = 1) (hb : d168288 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35567 q ha hb
    | true =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167387 q = 1) (hb : d168289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167388 q = 1) (hb : d168290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167389 q = 1) (hb : d168291 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52708 q = 1) (hb : d168288 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35553 q ha hb
    | true =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137362 q = 1) (hb : d168289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137362, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137362, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137363 q = 1) (hb : d168290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137363, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137363, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137365 q = 1) (hb : d168292 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137365, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137365, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167390 q = 1) (hb : d168293 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167390, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167390, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167391 q = 1) (hb : d168294 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167391, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167391, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35569 (p : Pattern) (ha : d167397 p = 1) (hb : d168304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167395 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167396 q = 1) (hb : d168303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167396, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167396, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167397 q = 1) (hb : d168304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167397, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167397, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35570 (p : Pattern) (ha : d167403 p = 1) (hb : d168314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167398 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35569 q ha hb
    | true =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
  have h2 (q : Pattern) (ha : d167399 q = 1) (hb : d168310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167399, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167399, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167400 q = 1) (hb : d168311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167400, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167400, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167401 q = 1) (hb : d168312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167401, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167401, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167402 q = 1) (hb : d168313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167402, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167402, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167403 q = 1) (hb : d168314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167403, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167403, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35571 (p : Pattern) (ha : d167406 p = 1) (hb : d168317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167395 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167396 q = 1) (hb : d168303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167396, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167396, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167406 q = 1) (hb : d168317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167406, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167406, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35572 (p : Pattern) (ha : d167412 p = 1) (hb : d168324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167398 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35569 q ha hb
    | true =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
  have h2 (q : Pattern) (ha : d167399 q = 1) (hb : d168310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167399, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167399, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167400 q = 1) (hb : d168311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167400, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167400, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167401 q = 1) (hb : d168312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167401, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167401, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167402 q = 1) (hb : d168313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167402, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167402, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167407 q = 1) (hb : d168319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35571 q ha hb
    | true =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35556 q ha hb
  have h7 (q : Pattern) (ha : d167408 q = 1) (hb : d168320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167408, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167408, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167409 q = 1) (hb : d168321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167409, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167409, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d167410 q = 1) (hb : d168322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167410, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167410, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167411 q = 1) (hb : d168323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167411, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167411, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167412 q = 1) (hb : d168324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167412, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167412, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35573 (p : Pattern) (ha : d137404 p = 1) (hb : d168331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d168306 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137403 q = 1) (hb : d168330 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137403, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137403, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137404 q = 1) (hb : d168331 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137404, d168331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137404, d168331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35574 (p : Pattern) (ha : d137414 p = 1) (hb : d168341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137412 q = 1) (hb : d168339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137412, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137412, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137413 q = 1) (hb : d168340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137413, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137413, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137414 q = 1) (hb : d168341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137414, d168341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137414, d168341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35575 (p : Pattern) (ha : d167417 p = 1) (hb : d168329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167395 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167416 q = 1) (hb : d168328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167416, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167416, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167417 q = 1) (hb : d168329 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167417, d168329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167417, d168329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35576 (p : Pattern) (ha : d167424 p = 1) (hb : d168338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167422 q = 1) (hb : d168336 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167422, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167422, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167423 q = 1) (hb : d168337 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167423, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167423, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167424 q = 1) (hb : d168338 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167424, d168338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167424, d168338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35577 (p : Pattern) (ha : d9762 p = 1) (hb : d52680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9759 q = 1) (hb : d52671 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9759, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52507 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9760 q = 1) (hb : d52672 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9760, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9760, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9761 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9761, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9761, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9581 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35525 q ha hb
    | true =>
      simp only [d9581, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9582 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9582, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9749 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9749, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9749, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9750 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9750, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9750, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9751 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9751, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9751, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9762 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9762, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9762, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35578 (p : Pattern) (ha : d52695 p = 1) (hb : d168345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9763 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35577 q ha hb
    | true =>
      simp only [d9763, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9765 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9765, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14836 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14836, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14837 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14837, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14838 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14838, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14838, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52695 q = 1) (hb : d168345 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35579 (p : Pattern) (ha : d9777 p = 1) (hb : d101334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101292 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9581 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9582 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9582, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9768 q = 1) (hb : d101331 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9768, d101331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9769 q = 1) (hb : d101332 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9769, d101332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9770 q = 1) (hb : d101333 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9770, d101333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d9772 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h10 (q : Pattern) (ha : d9773 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9452 q = 1) (hb : d101067 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7946 q ha hb
    | true =>
      simp only [d9452, d101067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d9453 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9453, d101068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9774 q = 1) (hb : d101295 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9774, d101295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9775 q = 1) (hb : d101296 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9775, d101296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d9776 q = 1) (hb : d101297 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9776, d101297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d9777 q = 1) (hb : d101334 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9777, d101334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9777, d101334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35580 (p : Pattern) (ha : d113359 p = 1) (hb : d168283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9778 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35579 q ha hb
    | true =>
      simp only [d9778, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9780 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9780, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14758 q = 1) (hb : d113352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14758, d113352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14759 q = 1) (hb : d113353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14759, d113353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14760 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14760, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14760, d113359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113359 q = 1) (hb : d168283 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35581 (p : Pattern) (ha : d167432 p = 1) (hb : d168351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52695 q = 1) (hb : d168346 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35578 q ha hb
    | true =>
      simp only [d168346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137418 q = 1) (hb : d168347 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137418, d168347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137418, d168347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137419 q = 1) (hb : d168348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137419, d168348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137419, d168348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113359 q = 1) (hb : d168284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35580 q ha hb
    | true =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167428 q = 1) (hb : d168285 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167428, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167428, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167429 q = 1) (hb : d168286 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167429, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167429, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167430 q = 1) (hb : d168349 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167430, d168349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167430, d168349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52706 q = 1) (hb : d168284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35565 q ha hb
    | true =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137360 q = 1) (hb : d168285 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137361 q = 1) (hb : d168286 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69112 q = 1) (hb : d168288 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35567 q ha hb
    | true =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167387 q = 1) (hb : d168289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167388 q = 1) (hb : d168290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167389 q = 1) (hb : d168291 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d167431 q = 1) (hb : d168350 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167431, d168350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167431, d168350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167432 q = 1) (hb : d168351 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167432, d168351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167432, d168351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35582 (p : Pattern) (ha : d167437 p = 1) (hb : d168294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52706 q = 1) (hb : d168284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35565 q ha hb
    | true =>
      simp only [d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137360 q = 1) (hb : d168285 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137360, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137361 q = 1) (hb : d168286 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137361, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69112 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69112 q = 1) (hb : d168288 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35567 q ha hb
    | true =>
      simp only [d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167387 q = 1) (hb : d168289 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167387, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167388 q = 1) (hb : d168290 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167388, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167389 q = 1) (hb : d168291 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167389, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167435 q = 1) (hb : d168292 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167435, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167435, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167436 q = 1) (hb : d168293 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167436, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167436, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167437 q = 1) (hb : d168294 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167437, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167437, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35583 (p : Pattern) (ha : d167443 p = 1) (hb : d168357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167433 q = 1) (hb : d168352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167433, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35581 q ha hb
    | true =>
      simp only [d167433, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167434 q = 1) (hb : d168353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167434, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167434, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167438 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35582 q ha hb
    | true =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167439 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167440 q = 1) (hb : d168354 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167440, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167440, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167441 q = 1) (hb : d168355 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167441, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167441, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167442 q = 1) (hb : d168356 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167442, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167442, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167443 q = 1) (hb : d168357 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167443, d168357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167443, d168357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35584 (p : Pattern) (ha : d167447 p = 1) (hb : d168304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167438 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35582 q ha hb
    | true =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167439 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167444 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167444, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167444, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167445 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167445, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167445, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167446 q = 1) (hb : d168303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167446, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167446, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167447 q = 1) (hb : d168304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167447, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167447, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35585 (p : Pattern) (ha : d167453 p = 1) (hb : d168363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167450 q = 1) (hb : d168360 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167450, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167450, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167451 q = 1) (hb : d168361 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167451, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167451, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167452 q = 1) (hb : d168362 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167452, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167452, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167453 q = 1) (hb : d168363 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167453, d168363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167453, d168363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35586 (p : Pattern) (ha : d167459 p = 1) (hb : d168369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167418 q = 1) (hb : d168332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167418, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35575 q ha hb
    | true =>
      simp only [d167418, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35573 q ha hb
  have h2 (q : Pattern) (ha : d167419 q = 1) (hb : d168333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167419, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167419, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167420 q = 1) (hb : d168334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167420, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167420, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167421 q = 1) (hb : d168335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167421, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167421, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167425 q = 1) (hb : d168342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167425, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35576 q ha hb
    | true =>
      simp only [d167425, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35574 q ha hb
  have h6 (q : Pattern) (ha : d167426 q = 1) (hb : d168343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167426, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167426, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167427 q = 1) (hb : d168344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167427, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167427, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167448 q = 1) (hb : d168358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167448, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35583 q ha hb
    | true =>
      simp only [d167448, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167449 q = 1) (hb : d168359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167449, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167449, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167454 q = 1) (hb : d168364 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167454, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35585 q ha hb
    | true =>
      simp only [d167454, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167455 q = 1) (hb : d168365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167455, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167455, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167456 q = 1) (hb : d168366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167456, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167456, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167457 q = 1) (hb : d168367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167457, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167457, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167458 q = 1) (hb : d168368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167458, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167458, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167459 q = 1) (hb : d168369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167459, d168369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167459, d168369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35587 (p : Pattern) (ha : d137449 p = 1) (hb : d168371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137379 q = 1) (hb : d168306 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137379, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137403 q = 1) (hb : d168330 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137403, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137403, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137449 q = 1) (hb : d168371 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137449, d168371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137449, d168371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35588 (p : Pattern) (ha : d137455 p = 1) (hb : d168377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137378 q = 1) (hb : d168305 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137378, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137412 q = 1) (hb : d168339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137412, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137412, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137413 q = 1) (hb : d168340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137413, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137413, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137455 q = 1) (hb : d168377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137455, d168377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137455, d168377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35589 (p : Pattern) (ha : d167460 p = 1) (hb : d168370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167395 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167395, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167416 q = 1) (hb : d168328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167416, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167416, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167460 q = 1) (hb : d168370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167460, d168370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167460, d168370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35590 (p : Pattern) (ha : d167465 p = 1) (hb : d168376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167394 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167394, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167422 q = 1) (hb : d168336 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167422, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167422, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167423 q = 1) (hb : d168337 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167423, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167423, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167465 q = 1) (hb : d168376 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167465, d168376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167465, d168376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35591 (p : Pattern) (ha : d167469 p = 1) (hb : d168381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167433 q = 1) (hb : d168352 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167433, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35581 q ha hb
    | true =>
      simp only [d167433, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167434 q = 1) (hb : d168353 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167434, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167434, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167438 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35582 q ha hb
    | true =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167439 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167440 q = 1) (hb : d168354 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167440, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167440, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167441 q = 1) (hb : d168355 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167441, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167441, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167442 q = 1) (hb : d168356 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167442, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167442, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167469 q = 1) (hb : d168381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167469, d168381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167469, d168381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35592 (p : Pattern) (ha : d167470 p = 1) (hb : d168317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167438 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35582 q ha hb
    | true =>
      simp only [d167438, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167439 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167439, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137372 q = 1) (hb : d168299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35554 q ha hb
    | true =>
      simp only [d137372, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137373 q = 1) (hb : d168300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137373, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167444 q = 1) (hb : d168301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167444, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167444, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167445 q = 1) (hb : d168302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167445, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167445, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167446 q = 1) (hb : d168303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167446, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167446, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167470 q = 1) (hb : d168317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167470, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167470, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35593 (p : Pattern) (ha : d167473 p = 1) (hb : d168384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167392 q = 1) (hb : d168295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35568 q ha hb
    | true =>
      simp only [d167392, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167393 q = 1) (hb : d168296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167393, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167450 q = 1) (hb : d168360 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167450, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167450, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167451 q = 1) (hb : d168361 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167451, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167451, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167452 q = 1) (hb : d168362 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167452, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167452, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167473 q = 1) (hb : d168384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167473, d168384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167473, d168384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35594 (p : Pattern) (ha : d167479 p = 1) (hb : d168390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167418 q = 1) (hb : d168332 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167418, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35575 q ha hb
    | true =>
      simp only [d167418, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35573 q ha hb
  have h2 (q : Pattern) (ha : d167419 q = 1) (hb : d168333 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167419, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167419, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167420 q = 1) (hb : d168334 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167420, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167420, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167421 q = 1) (hb : d168335 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167421, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167421, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167425 q = 1) (hb : d168342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167425, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35576 q ha hb
    | true =>
      simp only [d167425, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35574 q ha hb
  have h6 (q : Pattern) (ha : d167426 q = 1) (hb : d168343 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167426, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167426, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167427 q = 1) (hb : d168344 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167427, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167427, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167448 q = 1) (hb : d168358 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167448, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35583 q ha hb
    | true =>
      simp only [d167448, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167449 q = 1) (hb : d168359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167449, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167449, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167454 q = 1) (hb : d168364 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167454, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35585 q ha hb
    | true =>
      simp only [d167454, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167455 q = 1) (hb : d168365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167455, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167455, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167456 q = 1) (hb : d168366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167456, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167456, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167457 q = 1) (hb : d168367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167457, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167457, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167458 q = 1) (hb : d168368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167458, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167458, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167461 q = 1) (hb : d168372 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167461, d168372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35589 q ha hb
    | true =>
      simp only [d167461, d168372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35587 q ha hb
  have h17 (q : Pattern) (ha : d167462 q = 1) (hb : d168373 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167462, d168373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167462, d168373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167463 q = 1) (hb : d168374 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167463, d168374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167463, d168374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d167464 q = 1) (hb : d168375 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167464, d168375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167464, d168375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167466 q = 1) (hb : d168378 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167466, d168378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35590 q ha hb
    | true =>
      simp only [d167466, d168378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35588 q ha hb
  have h21 (q : Pattern) (ha : d167467 q = 1) (hb : d168379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167467, d168379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167467, d168379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d167468 q = 1) (hb : d168380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167468, d168380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167468, d168380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167471 q = 1) (hb : d168382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167471, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35591 q ha hb
    | true =>
      simp only [d167471, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35592 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d167407 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d167472 q = 1) (hb : d168383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167472, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d167472, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d167474 q = 1) (hb : d168385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167474, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35593 q ha hb
    | true =>
      simp only [d167474, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d167475 q = 1) (hb : d168386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167475, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d167475, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d167476 q = 1) (hb : d168387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167476, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d167476, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d167477 q = 1) (hb : d168388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167477, d168388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d167477, d168388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d167478 q = 1) (hb : d168389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167478, d168389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167478, d168389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d167479 q = 1) (hb : d168390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167479, d168390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167479, d168390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35595 (p : Pattern) (ha : d167486 p = 1) (hb : d168397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167481 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167481, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35584 q ha hb
    | true =>
      simp only [d167481, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
  have h2 (q : Pattern) (ha : d167482 q = 1) (hb : d168310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167482, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167482, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167483 q = 1) (hb : d168311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167483, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167483, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167484 q = 1) (hb : d168312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167484, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167484, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167485 q = 1) (hb : d168313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167485, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167485, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137470 q = 1) (hb : d168392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137470, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
    | true =>
      simp only [d137470, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137471 q = 1) (hb : d168393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137471, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137471, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137472 q = 1) (hb : d168394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137472, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137472, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137473 q = 1) (hb : d168395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137473, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137473, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137474 q = 1) (hb : d168396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137474, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137474, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167486 q = 1) (hb : d168397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167486, d168397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167486, d168397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35596 (p : Pattern) (ha : d167493 p = 1) (hb : d168410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167471 q = 1) (hb : d168382 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167471, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35591 q ha hb
    | true =>
      simp only [d167471, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35592 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167407 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167472 q = 1) (hb : d168383 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167472, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167472, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167474 q = 1) (hb : d168385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167474, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35593 q ha hb
    | true =>
      simp only [d167474, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167475 q = 1) (hb : d168386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167475, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167475, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167476 q = 1) (hb : d168387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167476, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167476, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167491 q = 1) (hb : d168408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167491, d168408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167491, d168408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167492 q = 1) (hb : d168409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167492, d168409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167492, d168409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167493 q = 1) (hb : d168410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167493, d168410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167493, d168410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35597 (p : Pattern) (ha : d52877 p = 1) (hb : d168418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14987 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14987, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35577 q ha hb
  have h3 (q : Pattern) (ha : d9763 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35577 q ha hb
    | true =>
      simp only [d9763, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14988 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14988, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9765 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9765, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14989 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14989, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14990 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14990, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14991 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14991, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14991, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52877 q = 1) (hb : d168418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35598 (p : Pattern) (ha : d52883 p = 1) (hb : d168422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14994 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14994, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35564 q ha hb
  have h3 (q : Pattern) (ha : d9778 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35564 q ha hb
    | true =>
      simp only [d9778, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14995 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14995, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9780 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9780, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14996 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14996, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14997 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14997, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14998 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14998, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14998, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52883 q = 1) (hb : d168422 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35599 (p : Pattern) (ha : d76094 p = 1) (hb : d168427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15004 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15004, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35566 q ha hb
  have h3 (q : Pattern) (ha : d9800 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35566 q ha hb
    | true =>
      simp only [d9800, d69108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15005 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15005, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9802 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9802, d69109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15006 q = 1) (hb : d76092 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15006, d76092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15007 q = 1) (hb : d76093 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15007, d76093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15008 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15008, d76094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76094 q = 1) (hb : d168427 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35600 (p : Pattern) (ha : d113460 p = 1) (hb : d168422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14994 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14994, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35579 q ha hb
  have h3 (q : Pattern) (ha : d9778 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35579 q ha hb
    | true =>
      simp only [d9778, d101335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d14995 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14995, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9780 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9780, d101337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d14996 q = 1) (hb : d113454 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14996, d113454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14997 q = 1) (hb : d113455 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14997, d113455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14998 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14998, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14998, d113460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113460 q = 1) (hb : d168422 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35601 (p : Pattern) (ha : d167506 p = 1) (hb : d168433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52877 q = 1) (hb : d168419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35597 q ha hb
    | true =>
      simp only [d168419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137496 q = 1) (hb : d168420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137496, d168420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137496, d168420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137497 q = 1) (hb : d168421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137497, d168421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137497, d168421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113460 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113460 q = 1) (hb : d168423 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35600 q ha hb
    | true =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167499 q = 1) (hb : d168424 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167499, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167499, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167500 q = 1) (hb : d168425 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167500, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167500, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167501 q = 1) (hb : d168426 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167501, d168426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167501, d168426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52883 q = 1) (hb : d168423 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35598 q ha hb
    | true =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137498 q = 1) (hb : d168424 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137499 q = 1) (hb : d168425 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76094 q = 1) (hb : d168428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35599 q ha hb
    | true =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167502 q = 1) (hb : d168429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167503 q = 1) (hb : d168430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167504 q = 1) (hb : d168431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d167505 q = 1) (hb : d168432 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167505, d168432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167505, d168432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167506 q = 1) (hb : d168433 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167506, d168433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167506, d168433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35602 (p : Pattern) (ha : d167511 p = 1) (hb : d168438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52883 q = 1) (hb : d168423 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35598 q ha hb
    | true =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137498 q = 1) (hb : d168424 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137499 q = 1) (hb : d168425 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76094 q = 1) (hb : d168428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35599 q ha hb
    | true =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167502 q = 1) (hb : d168429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167503 q = 1) (hb : d168430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167504 q = 1) (hb : d168431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167509 q = 1) (hb : d168436 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167509, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167509, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167510 q = 1) (hb : d168437 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167510, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167510, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167511 q = 1) (hb : d168438 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167511, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167511, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35603 (p : Pattern) (ha : d167517 p = 1) (hb : d168444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167507 q = 1) (hb : d168434 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167507, d168434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35601 q ha hb
    | true =>
      simp only [d167507, d168434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167508 q = 1) (hb : d168435 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167508, d168435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167508, d168435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167512 q = 1) (hb : d168439 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167512, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35602 q ha hb
    | true =>
      simp only [d167512, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167513 q = 1) (hb : d168440 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167513, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167513, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167514 q = 1) (hb : d168441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167514, d168441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167514, d168441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167515 q = 1) (hb : d168442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167515, d168442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167515, d168442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167516 q = 1) (hb : d168443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167516, d168443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167516, d168443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167517 q = 1) (hb : d168444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167517, d168444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167517, d168444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35604 (p : Pattern) (ha : d167521 p = 1) (hb : d168452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167512 q = 1) (hb : d168439 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167512, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35602 q ha hb
    | true =>
      simp only [d167512, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167513 q = 1) (hb : d168440 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167513, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167513, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137519 q = 1) (hb : d168447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35560 q ha hb
    | true =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137520 q = 1) (hb : d168448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167518 q = 1) (hb : d168449 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167518, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167518, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167519 q = 1) (hb : d168450 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167519, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167519, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167520 q = 1) (hb : d168451 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167520, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167520, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167521 q = 1) (hb : d168452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167521, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167521, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35605 (p : Pattern) (ha : d167524 p = 1) (hb : d168438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52883 q = 1) (hb : d168423 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35598 q ha hb
    | true =>
      simp only [d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137498 q = 1) (hb : d168424 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137498, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137499 q = 1) (hb : d168425 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137499, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76094 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76094 q = 1) (hb : d168428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35599 q ha hb
    | true =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167502 q = 1) (hb : d168429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167502, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167503 q = 1) (hb : d168430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167503, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167504 q = 1) (hb : d168431 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167504, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52888 q = 1) (hb : d168428 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35559 q ha hb
    | true =>
      simp only [d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137501 q = 1) (hb : d168429 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137501, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137501, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137502 q = 1) (hb : d168430 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137502, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137502, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137508 q = 1) (hb : d168436 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137508, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137508, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167523 q = 1) (hb : d168437 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167523, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167523, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167524 q = 1) (hb : d168438 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167524, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167524, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35606 (p : Pattern) (ha : d167536 p = 1) (hb : d168458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167525 q = 1) (hb : d168439 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167525, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35605 q ha hb
    | true =>
      simp only [d167525, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167526 q = 1) (hb : d168440 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167526, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167526, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167533 q = 1) (hb : d168455 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167533, d168455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167533, d168455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167534 q = 1) (hb : d168456 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167534, d168456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167534, d168456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167535 q = 1) (hb : d168457 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167535, d168457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167535, d168457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167536 q = 1) (hb : d168458 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167536, d168458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167536, d168458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35607 (p : Pattern) (ha : d167542 p = 1) (hb : d168464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167522 q = 1) (hb : d168453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167522, d168453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35603 q ha hb
    | true =>
      simp only [d167522, d168453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35604 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167531 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167532 q = 1) (hb : d168454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167532, d168454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167532, d168454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167537 q = 1) (hb : d168459 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167537, d168459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35606 q ha hb
    | true =>
      simp only [d167537, d168459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167538 q = 1) (hb : d168460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167538, d168460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167538, d168460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167539 q = 1) (hb : d168461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167539, d168461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167539, d168461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167540 q = 1) (hb : d168462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167540, d168462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167540, d168462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167541 q = 1) (hb : d168463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167541, d168463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167541, d168463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167542 q = 1) (hb : d168464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167542, d168464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167542, d168464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35608 (p : Pattern) (ha : d167548 p = 1) (hb : d168481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167404 q = 1) (hb : d168315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167404, d168315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167404, d168315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35570 q ha hb
  have h2 (q : Pattern) (ha : d167405 q = 1) (hb : d168316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167405, d168316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167405, d168316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167413 q = 1) (hb : d168325 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167413, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35570 q ha hb
    | true =>
      simp only [d167413, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35572 q ha hb
  have h4 (q : Pattern) (ha : d167414 q = 1) (hb : d168326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167414, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167414, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167415 q = 1) (hb : d168327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167415, d168327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167415, d168327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167480 q = 1) (hb : d168391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167480, d168391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35586 q ha hb
    | true =>
      simp only [d167480, d168391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35594 q ha hb
  have h7 (q : Pattern) (ha : d167487 q = 1) (hb : d168404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167487, d168404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35595 q ha hb
    | true =>
      simp only [d167487, d168404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35557 q ha hb
  have h8 (q : Pattern) (ha : d167488 q = 1) (hb : d168405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167488, d168405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167488, d168405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167489 q = 1) (hb : d168406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167489, d168406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167489, d168406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d167490 q = 1) (hb : d168407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167490, d168407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167490, d168407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167494 q = 1) (hb : d168411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167494, d168411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167494, d168411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35596 q ha hb
  have h12 (q : Pattern) (ha : d137491 q = 1) (hb : d168413 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137491, d168413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137491, d168413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35558 q ha hb
  have h13 (q : Pattern) (ha : d167495 q = 1) (hb : d168414 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167495, d168414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167495, d168414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167496 q = 1) (hb : d168415 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167496, d168415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167496, d168415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167497 q = 1) (hb : d168416 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167497, d168416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d167497, d168416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d167498 q = 1) (hb : d168417 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167498, d168417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167498, d168417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167543 q = 1) (hb : d168465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167543, d168465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167543, d168465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35607 q ha hb
  have h18 (q : Pattern) (ha : d137556 q = 1) (hb : d168476 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137556, d168476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137556, d168476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35562 q ha hb
  have h19 (q : Pattern) (ha : d167544 q = 1) (hb : d168477 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167544, d168477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167544, d168477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167545 q = 1) (hb : d168478 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167545, d168478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167545, d168478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d167546 q = 1) (hb : d168479 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167546, d168479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d167546, d168479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d167547 q = 1) (hb : d168480 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167547, d168480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167547, d168480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167548 q = 1) (hb : d168481 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167548, d168481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167548, d168481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35609 (p : Pattern) (ha : d167554 p = 1) (hb : d168487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167549 q = 1) (hb : d168482 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167549, d168482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167549, d168482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35608 q ha hb
  have h2 (q : Pattern) (ha : d167550 q = 1) (hb : d168483 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167550, d168483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167550, d168483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167551 q = 1) (hb : d168484 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167551, d168484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167551, d168484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167552 q = 1) (hb : d168485 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167552, d168485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167552, d168485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167553 q = 1) (hb : d168486 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167553, d168486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167553, d168486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167554 q = 1) (hb : d168487 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167554, d168487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167554, d168487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35610 (p : Pattern) (ha : d5122 p = 1) (hb : d52989 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309 q = 1) (hb : d52108 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d825 q = 1) (hb : d52961 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d52961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d825, d52961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5121 q = 1) (hb : d52973 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5121, d52973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5121, d52973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5122 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5122, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5122, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro35611 (p : Pattern) (ha : d10084 p = 1) (hb : d53022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10057 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35610 q ha hb
    | true =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10058 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10080 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10080, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10081 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10082 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10082, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10083 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10083, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5128 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15069 q ha hb
  have h16 (q : Pattern) (ha : d5129 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5129, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h19 (q : Pattern) (ha : d5130 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5130, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d5131 q = 1) (hb : d53020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d5131, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d5132 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d5132, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h23 (q : Pattern) (ha : d10084 q = 1) (hb : d53022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10084, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10084, d53022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35612 (p : Pattern) (ha : d53029 p = 1) (hb : d168495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10085 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35611 q ha hb
    | true =>
      simp only [d10085, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10087 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10087, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15156 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15156, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15157 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15157, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15158 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15158, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53029 q = 1) (hb : d168495 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35613 (p : Pattern) (ha : d137582 p = 1) (hb : d168506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53029 q = 1) (hb : d168496 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35612 q ha hb
    | true =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137573 q = 1) (hb : d168497 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137574 q = 1) (hb : d168498 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137576 q = 1) (hb : d168500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137576, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137576, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137581 q = 1) (hb : d168505 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137581, d168505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137581, d168505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137582 q = 1) (hb : d168506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137582, d168506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137582, d168506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35614 (p : Pattern) (ha : d137592 p = 1) (hb : d168516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d168514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137591 q = 1) (hb : d168515 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137591, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137591, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137592 q = 1) (hb : d168516 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137592, d168516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137592, d168516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35615 (p : Pattern) (ha : d137602 p = 1) (hb : d168526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d168514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137591 q = 1) (hb : d168515 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137591, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137591, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137602 q = 1) (hb : d168526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137602, d168526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137602, d168526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35616 (p : Pattern) (ha : d137692 p = 1) (hb : d168611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137681 q = 1) (hb : d168600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137681, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
    | true =>
      simp only [d137681, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137682 q = 1) (hb : d168601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137682, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137682, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137683 q = 1) (hb : d168602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137683, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137683, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137684 q = 1) (hb : d168603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137684, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137684, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137685 q = 1) (hb : d168604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137685, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137685, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137687 q = 1) (hb : d168606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137687, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35615 q ha hb
    | true =>
      simp only [d137687, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137688 q = 1) (hb : d168607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137688, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137688, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137689 q = 1) (hb : d168608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137689, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137689, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137690 q = 1) (hb : d168609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137690, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137690, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137691 q = 1) (hb : d168610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137691, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137691, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137692 q = 1) (hb : d168611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137692, d168611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137692, d168611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35617 (p : Pattern) (ha : d137701 p = 1) (hb : d168620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137687 q = 1) (hb : d168606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137687, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35615 q ha hb
    | true =>
      simp only [d137687, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137688 q = 1) (hb : d168607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137688, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137688, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137689 q = 1) (hb : d168608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137689, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137689, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137690 q = 1) (hb : d168609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137690, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137690, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137691 q = 1) (hb : d168610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137691, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137691, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137701 q = 1) (hb : d168620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137701, d168620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137701, d168620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35618 (p : Pattern) (ha : d53203 p = 1) (hb : d168635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15397 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15397, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35611 q ha hb
  have h3 (q : Pattern) (ha : d10085 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35611 q ha hb
    | true =>
      simp only [d10085, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15398 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15398, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10087 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10087, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15399 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15399, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15400 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15400, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15401 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15401, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d53203 q = 1) (hb : d168635 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35619 (p : Pattern) (ha : d137729 p = 1) (hb : d168654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53203 q = 1) (hb : d168636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35618 q ha hb
    | true =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137712 q = 1) (hb : d168637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137713 q = 1) (hb : d168638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137719 q = 1) (hb : d168644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137719, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137719, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137728 q = 1) (hb : d168653 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137728, d168653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137728, d168653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137729 q = 1) (hb : d168654 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137729, d168654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137729, d168654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35620 (p : Pattern) (ha : d137740 p = 1) (hb : d168677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137730 q = 1) (hb : d168655 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35619 q ha hb
    | true =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137731 q = 1) (hb : d168656 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137737 q = 1) (hb : d168674 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137737, d168674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137737, d168674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137738 q = 1) (hb : d168675 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137738, d168675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137738, d168675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137739 q = 1) (hb : d168676 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137739, d168676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137739, d168676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137740 q = 1) (hb : d168677 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137740, d168677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137740, d168677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35621 (p : Pattern) (ha : d137766 p = 1) (hb : d168683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137761 q = 1) (hb : d168678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137761, d168678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35620 q ha hb
    | true =>
      simp only [d137761, d168678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137762 q = 1) (hb : d168679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137762, d168679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137762, d168679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137763 q = 1) (hb : d168680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137763, d168680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137763, d168680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137764 q = 1) (hb : d168681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137764, d168681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137764, d168681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137765 q = 1) (hb : d168682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137765, d168682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137765, d168682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137766 q = 1) (hb : d168683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137766, d168683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137766, d168683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35622 (p : Pattern) (ha : d10054 p = 1) (hb : d52983 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2005 q = 1) (hb : d52965 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, d52965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, d52965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2006 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, d52966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2006, d52966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52982 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10054 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d10054, d52983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10054, d52983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35623 (p : Pattern) (ha : d10062 p = 1) (hb : d53010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10051 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52992 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10052 q = 1) (hb : d52993 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10052, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10053 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10053, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52980 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10055 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10055, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35622 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10056 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10056, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10057 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35610 q ha hb
    | true =>
      simp only [d10057, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10058 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10058, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10059 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10059, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10059, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10060 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10060, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10060, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10061 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10061, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10061, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d10062 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10062, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10062, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro35624 (p : Pattern) (ha : d53027 p = 1) (hb : d168491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10063 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35623 q ha hb
    | true =>
      simp only [d10063, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10065 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10065, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15151 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15151, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15152 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15152, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15153 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15153, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15153, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53027 q = 1) (hb : d168491 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35625 (p : Pattern) (ha : d10084 p = 1) (hb : d69220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53004 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10057 q = 1) (hb : d69210 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d10057, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10058 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10058, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10080 q = 1) (hb : d69212 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10080, d69212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10081 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10081, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10082 q = 1) (hb : d69213 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10082, d69213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10083 q = 1) (hb : d69214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10083, d69214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
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
  have h16 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d5130 q = 1) (hb : d69217 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d5131 q = 1) (hb : d69218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d5132 q = 1) (hb : d69219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d10084 q = 1) (hb : d69220 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10084, d69220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10084, d69220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro35626 (p : Pattern) (ha : d69225 p = 1) (hb : d168495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10085 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35625 q ha hb
    | true =>
      simp only [d10085, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10087 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10087, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15156 q = 1) (hb : d69223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15156, d69223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15157 q = 1) (hb : d69224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15157, d69224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15158 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15158, d69225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69225 q = 1) (hb : d168495 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35627 (p : Pattern) (ha : d167562 p = 1) (hb : d168502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53027 q = 1) (hb : d168492 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35624 q ha hb
    | true =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137571 q = 1) (hb : d168493 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137572 q = 1) (hb : d168494 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69225 q = 1) (hb : d168496 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35626 q ha hb
    | true =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167558 q = 1) (hb : d168497 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167559 q = 1) (hb : d168498 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167560 q = 1) (hb : d168499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53029 q = 1) (hb : d168496 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35612 q ha hb
    | true =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137573 q = 1) (hb : d168497 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137574 q = 1) (hb : d168498 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137576 q = 1) (hb : d168500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137576, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137576, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167561 q = 1) (hb : d168501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167561, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167561, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167562 q = 1) (hb : d168502 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167562, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167562, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35628 (p : Pattern) (ha : d167568 p = 1) (hb : d168512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167566 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167567 q = 1) (hb : d168511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167567, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167567, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167568 q = 1) (hb : d168512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167568, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167568, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35629 (p : Pattern) (ha : d167574 p = 1) (hb : d168522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167569 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35628 q ha hb
    | true =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
  have h2 (q : Pattern) (ha : d167570 q = 1) (hb : d168518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167570, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167570, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167571 q = 1) (hb : d168519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167571, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167571, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167572 q = 1) (hb : d168520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167572, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167572, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167573 q = 1) (hb : d168521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167573, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167573, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167574 q = 1) (hb : d168522 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167574, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167574, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35630 (p : Pattern) (ha : d167577 p = 1) (hb : d168525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167566 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167567 q = 1) (hb : d168511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167567, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167567, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167577 q = 1) (hb : d168525 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167577, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167577, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35631 (p : Pattern) (ha : d167583 p = 1) (hb : d168532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167569 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35628 q ha hb
    | true =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
  have h2 (q : Pattern) (ha : d167570 q = 1) (hb : d168518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167570, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167570, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167571 q = 1) (hb : d168519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167571, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167571, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167572 q = 1) (hb : d168520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167572, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167572, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167573 q = 1) (hb : d168521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167573, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167573, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167578 q = 1) (hb : d168527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35630 q ha hb
    | true =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35615 q ha hb
  have h7 (q : Pattern) (ha : d167579 q = 1) (hb : d168528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167579, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167579, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167580 q = 1) (hb : d168529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167580, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167580, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d167581 q = 1) (hb : d168530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167581, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167581, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167582 q = 1) (hb : d168531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167582, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167582, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167583 q = 1) (hb : d168532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167583, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167583, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35632 (p : Pattern) (ha : d137615 p = 1) (hb : d168539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d168514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137614 q = 1) (hb : d168538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137614, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137614, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137615 q = 1) (hb : d168539 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137615, d168539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137615, d168539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35633 (p : Pattern) (ha : d137625 p = 1) (hb : d168549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137623 q = 1) (hb : d168547 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137623, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137623, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137624 q = 1) (hb : d168548 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137624, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137624, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137625 q = 1) (hb : d168549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137625, d168549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137625, d168549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35634 (p : Pattern) (ha : d167588 p = 1) (hb : d168537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167566 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167587 q = 1) (hb : d168536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167587, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167587, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167588 q = 1) (hb : d168537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167588, d168537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167588, d168537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35635 (p : Pattern) (ha : d167595 p = 1) (hb : d168546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167593 q = 1) (hb : d168544 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167593, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167593, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167594 q = 1) (hb : d168545 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167594, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167594, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167595 q = 1) (hb : d168546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167595, d168546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167595, d168546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35636 (p : Pattern) (ha : d10045 p = 1) (hb : d52995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10042 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52977 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10043 q = 1) (hb : d52978 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10043, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10044 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10044, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10045 q = 1) (hb : d52995 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10045, d52995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10045, d52995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35637 (p : Pattern) (ha : d53015 p = 1) (hb : d168553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10046 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
    | true =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10048 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15229 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15229, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15230 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15230, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15231 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15231, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15231, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53015 q = 1) (hb : d168553 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35638 (p : Pattern) (ha : d10062 p = 1) (hb : d101525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10051 q = 1) (hb : d101522 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10052 q = 1) (hb : d101523 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10052, d101523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d101524 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10053, d101524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h9 (q : Pattern) (ha : d10056 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10057 q = 1) (hb : d101484 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7963 q ha hb
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10058 q = 1) (hb : d101485 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d10059 q = 1) (hb : d101486 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10060 q = 1) (hb : d101487 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10061 q = 1) (hb : d101488 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d10062 q = 1) (hb : d101525 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10062, d101525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10062, d101525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35639 (p : Pattern) (ha : d113615 p = 1) (hb : d168491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10063 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35638 q ha hb
    | true =>
      simp only [d10063, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10065 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10065, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15151 q = 1) (hb : d113608 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15151, d113608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15152 q = 1) (hb : d113609 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15152, d113609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15153 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15153, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15153, d113615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113615 q = 1) (hb : d168491 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35640 (p : Pattern) (ha : d167603 p = 1) (hb : d168559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53015 q = 1) (hb : d168554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35637 q ha hb
    | true =>
      simp only [d168554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137629 q = 1) (hb : d168555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137629, d168555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137629, d168555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137630 q = 1) (hb : d168556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137630, d168556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137630, d168556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113615 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113615 q = 1) (hb : d168492 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35639 q ha hb
    | true =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167599 q = 1) (hb : d168493 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167599, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167599, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167600 q = 1) (hb : d168494 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167600, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167600, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167601 q = 1) (hb : d168557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167601, d168557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167601, d168557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53027 q = 1) (hb : d168492 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35624 q ha hb
    | true =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137571 q = 1) (hb : d168493 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137572 q = 1) (hb : d168494 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69225 q = 1) (hb : d168496 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35626 q ha hb
    | true =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167558 q = 1) (hb : d168497 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167559 q = 1) (hb : d168498 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167560 q = 1) (hb : d168499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d167602 q = 1) (hb : d168558 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167602, d168558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167602, d168558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167603 q = 1) (hb : d168559 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167603, d168559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167603, d168559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35641 (p : Pattern) (ha : d167608 p = 1) (hb : d168502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53027 q = 1) (hb : d168492 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35624 q ha hb
    | true =>
      simp only [d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137571 q = 1) (hb : d168493 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137572 q = 1) (hb : d168494 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69225 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69225 q = 1) (hb : d168496 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35626 q ha hb
    | true =>
      simp only [d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167558 q = 1) (hb : d168497 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167558, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167559 q = 1) (hb : d168498 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167559, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167560 q = 1) (hb : d168499 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167560, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167606 q = 1) (hb : d168500 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167606, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167606, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167607 q = 1) (hb : d168501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167607, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167607, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167608 q = 1) (hb : d168502 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167608, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167608, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35642 (p : Pattern) (ha : d167614 p = 1) (hb : d168565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167604 q = 1) (hb : d168560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167604, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35640 q ha hb
    | true =>
      simp only [d167604, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167605 q = 1) (hb : d168561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167605, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167605, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167609 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35641 q ha hb
    | true =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167610 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167611 q = 1) (hb : d168562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167611, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167611, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167612 q = 1) (hb : d168563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167612, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167612, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167613 q = 1) (hb : d168564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167613, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167613, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167614 q = 1) (hb : d168565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167614, d168565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167614, d168565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35643 (p : Pattern) (ha : d167618 p = 1) (hb : d168512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167609 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35641 q ha hb
    | true =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167610 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167615 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167615, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167615, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167616 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167616, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167616, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167617 q = 1) (hb : d168511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167617, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167617, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167618 q = 1) (hb : d168512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167618, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167618, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35644 (p : Pattern) (ha : d167624 p = 1) (hb : d168571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167621 q = 1) (hb : d168568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167621, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167621, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167622 q = 1) (hb : d168569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167622, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167622, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167623 q = 1) (hb : d168570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167623, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167623, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167624 q = 1) (hb : d168571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167624, d168571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167624, d168571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35645 (p : Pattern) (ha : d167630 p = 1) (hb : d168577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167589 q = 1) (hb : d168540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167589, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35634 q ha hb
    | true =>
      simp only [d167589, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35632 q ha hb
  have h2 (q : Pattern) (ha : d167590 q = 1) (hb : d168541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167590, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167590, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167591 q = 1) (hb : d168542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167591, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167591, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167592 q = 1) (hb : d168543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167592, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167592, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167596 q = 1) (hb : d168550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167596, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35635 q ha hb
    | true =>
      simp only [d167596, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35633 q ha hb
  have h6 (q : Pattern) (ha : d167597 q = 1) (hb : d168551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167597, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167597, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167598 q = 1) (hb : d168552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167598, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167598, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167619 q = 1) (hb : d168566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167619, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35642 q ha hb
    | true =>
      simp only [d167619, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167569 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167620 q = 1) (hb : d168567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167620, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167620, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167625 q = 1) (hb : d168572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167625, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35644 q ha hb
    | true =>
      simp only [d167625, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167626 q = 1) (hb : d168573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167626, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167626, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167627 q = 1) (hb : d168574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167627, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167627, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167628 q = 1) (hb : d168575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167628, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167628, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167629 q = 1) (hb : d168576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167629, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167629, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167630 q = 1) (hb : d168577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167630, d168577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167630, d168577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35646 (p : Pattern) (ha : d137660 p = 1) (hb : d168579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d168514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137614 q = 1) (hb : d168538 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137614, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137614, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137660 q = 1) (hb : d168579 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137660, d168579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137660, d168579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35647 (p : Pattern) (ha : d137666 p = 1) (hb : d168585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d168513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137623 q = 1) (hb : d168547 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137623, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137623, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137624 q = 1) (hb : d168548 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137624, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137624, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137666 q = 1) (hb : d168585 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137666, d168585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137666, d168585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35648 (p : Pattern) (ha : d167631 p = 1) (hb : d168578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167566 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167566, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167587 q = 1) (hb : d168536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167587, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167587, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167631 q = 1) (hb : d168578 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167631, d168578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167631, d168578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35649 (p : Pattern) (ha : d167636 p = 1) (hb : d168584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167565 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167565, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167593 q = 1) (hb : d168544 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167593, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167593, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167594 q = 1) (hb : d168545 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167594, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167594, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167636 q = 1) (hb : d168584 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167636, d168584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167636, d168584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35650 (p : Pattern) (ha : d167640 p = 1) (hb : d168589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167604 q = 1) (hb : d168560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167604, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35640 q ha hb
    | true =>
      simp only [d167604, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167605 q = 1) (hb : d168561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167605, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167605, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167609 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35641 q ha hb
    | true =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167610 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167611 q = 1) (hb : d168562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167611, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167611, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167612 q = 1) (hb : d168563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167612, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167612, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167613 q = 1) (hb : d168564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167613, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167613, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167640 q = 1) (hb : d168589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167640, d168589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167640, d168589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35651 (p : Pattern) (ha : d167641 p = 1) (hb : d168525 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167609 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35641 q ha hb
    | true =>
      simp only [d167609, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167610 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167610, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d168507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35613 q ha hb
    | true =>
      simp only [d137583, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d168508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167615 q = 1) (hb : d168509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167615, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167615, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167616 q = 1) (hb : d168510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167616, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167616, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167617 q = 1) (hb : d168511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167617, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167617, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167641 q = 1) (hb : d168525 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167641, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167641, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35652 (p : Pattern) (ha : d167644 p = 1) (hb : d168592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167563 q = 1) (hb : d168503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35627 q ha hb
    | true =>
      simp only [d167563, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167564 q = 1) (hb : d168504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167564, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167621 q = 1) (hb : d168568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167621, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167621, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167622 q = 1) (hb : d168569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167622, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167622, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167623 q = 1) (hb : d168570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167623, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167623, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167644 q = 1) (hb : d168592 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167644, d168592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167644, d168592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35653 (p : Pattern) (ha : d167650 p = 1) (hb : d168598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167589 q = 1) (hb : d168540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167589, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35634 q ha hb
    | true =>
      simp only [d167589, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35632 q ha hb
  have h2 (q : Pattern) (ha : d167590 q = 1) (hb : d168541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167590, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167590, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167591 q = 1) (hb : d168542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167591, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167591, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167592 q = 1) (hb : d168543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167592, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167592, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167596 q = 1) (hb : d168550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167596, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35635 q ha hb
    | true =>
      simp only [d167596, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35633 q ha hb
  have h6 (q : Pattern) (ha : d167597 q = 1) (hb : d168551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167597, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167597, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167598 q = 1) (hb : d168552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167598, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167598, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167619 q = 1) (hb : d168566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167619, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35642 q ha hb
    | true =>
      simp only [d167619, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35643 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167569 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167620 q = 1) (hb : d168567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167620, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167620, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167625 q = 1) (hb : d168572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167625, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35644 q ha hb
    | true =>
      simp only [d167625, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167626 q = 1) (hb : d168573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167626, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167626, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167627 q = 1) (hb : d168574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167627, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167627, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167628 q = 1) (hb : d168575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167628, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167628, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167629 q = 1) (hb : d168576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167629, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167629, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167632 q = 1) (hb : d168580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167632, d168580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35648 q ha hb
    | true =>
      simp only [d167632, d168580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35646 q ha hb
  have h17 (q : Pattern) (ha : d167633 q = 1) (hb : d168581 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167633, d168581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167633, d168581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167634 q = 1) (hb : d168582 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167634, d168582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167634, d168582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d167635 q = 1) (hb : d168583 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167635, d168583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167635, d168583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167637 q = 1) (hb : d168586 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167637, d168586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35649 q ha hb
    | true =>
      simp only [d167637, d168586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35647 q ha hb
  have h21 (q : Pattern) (ha : d167638 q = 1) (hb : d168587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167638, d168587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167638, d168587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d167639 q = 1) (hb : d168588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167639, d168588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167639, d168588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167642 q = 1) (hb : d168590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167642, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35650 q ha hb
    | true =>
      simp only [d167642, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35651 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d167578 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d167643 q = 1) (hb : d168591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167643, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d167643, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d167645 q = 1) (hb : d168593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167645, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35652 q ha hb
    | true =>
      simp only [d167645, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d167646 q = 1) (hb : d168594 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167646, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d167646, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d167647 q = 1) (hb : d168595 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167647, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d167647, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d167648 q = 1) (hb : d168596 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167648, d168596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d167648, d168596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d167649 q = 1) (hb : d168597 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167649, d168597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167649, d168597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d167650 q = 1) (hb : d168598 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167650, d168598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167650, d168598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35654 (p : Pattern) (ha : d167657 p = 1) (hb : d168605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167652 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167652, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35643 q ha hb
    | true =>
      simp only [d167652, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
  have h2 (q : Pattern) (ha : d167653 q = 1) (hb : d168518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167653, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167653, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167654 q = 1) (hb : d168519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167654, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167654, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167655 q = 1) (hb : d168520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167655, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167655, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167656 q = 1) (hb : d168521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167656, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167656, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137681 q = 1) (hb : d168600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137681, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
    | true =>
      simp only [d137681, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137682 q = 1) (hb : d168601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137682, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137682, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137683 q = 1) (hb : d168602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137683, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137683, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137684 q = 1) (hb : d168603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137684, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137684, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137685 q = 1) (hb : d168604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137685, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137685, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167657 q = 1) (hb : d168605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167657, d168605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167657, d168605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35655 (p : Pattern) (ha : d167664 p = 1) (hb : d168618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167642 q = 1) (hb : d168590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167642, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35650 q ha hb
    | true =>
      simp only [d167642, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35651 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167643 q = 1) (hb : d168591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167643, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167643, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167645 q = 1) (hb : d168593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167645, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35652 q ha hb
    | true =>
      simp only [d167645, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167646 q = 1) (hb : d168594 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167646, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167646, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167647 q = 1) (hb : d168595 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167647, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167647, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167662 q = 1) (hb : d168616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167662, d168616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167662, d168616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167663 q = 1) (hb : d168617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167663, d168617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167663, d168617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167664 q = 1) (hb : d168618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167664, d168618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167664, d168618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35656 (p : Pattern) (ha : d53192 p = 1) (hb : d168626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15380 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15380, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
  have h3 (q : Pattern) (ha : d10046 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35636 q ha hb
    | true =>
      simp only [d10046, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15381 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15381, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10048 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10048, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15382 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15382, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15383 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15383, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15384 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15384, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15384, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53192 q = 1) (hb : d168626 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35657 (p : Pattern) (ha : d53198 p = 1) (hb : d168630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15387 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15387, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35623 q ha hb
  have h3 (q : Pattern) (ha : d10063 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35623 q ha hb
    | true =>
      simp only [d10063, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15388 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15388, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10065 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10065, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15389 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15389, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15390 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15390, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15391 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15391, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15391, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53198 q = 1) (hb : d168630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35658 (p : Pattern) (ha : d76229 p = 1) (hb : d168635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15397 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15397, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35625 q ha hb
  have h3 (q : Pattern) (ha : d10085 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35625 q ha hb
    | true =>
      simp only [d10085, d69221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15398 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15398, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10087 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10087, d69222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15399 q = 1) (hb : d76227 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15399, d76227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15400 q = 1) (hb : d76228 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15400, d76228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15401 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15401, d76229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76229 q = 1) (hb : d168635 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35659 (p : Pattern) (ha : d113716 p = 1) (hb : d168630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15387 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15387, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35638 q ha hb
  have h3 (q : Pattern) (ha : d10063 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35638 q ha hb
    | true =>
      simp only [d10063, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15388 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15388, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10065 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10065, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15389 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15389, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15390 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15390, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15391 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15391, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15391, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113716 q = 1) (hb : d168630 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35660 (p : Pattern) (ha : d167677 p = 1) (hb : d168641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53192 q = 1) (hb : d168627 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35656 q ha hb
    | true =>
      simp only [d168627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137707 q = 1) (hb : d168628 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137707, d168628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137707, d168628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137708 q = 1) (hb : d168629 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137708, d168629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137708, d168629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113716 q = 1) (hb : d168631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35659 q ha hb
    | true =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167670 q = 1) (hb : d168632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167670, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167670, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167671 q = 1) (hb : d168633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167671, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167671, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167672 q = 1) (hb : d168634 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167672, d168634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167672, d168634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53198 q = 1) (hb : d168631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35657 q ha hb
    | true =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137709 q = 1) (hb : d168632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137710 q = 1) (hb : d168633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76229 q = 1) (hb : d168636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35658 q ha hb
    | true =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167673 q = 1) (hb : d168637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167674 q = 1) (hb : d168638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167675 q = 1) (hb : d168639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d167676 q = 1) (hb : d168640 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167676, d168640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167676, d168640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167677 q = 1) (hb : d168641 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167677, d168641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167677, d168641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35661 (p : Pattern) (ha : d167682 p = 1) (hb : d168646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53198 q = 1) (hb : d168631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35657 q ha hb
    | true =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137709 q = 1) (hb : d168632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137710 q = 1) (hb : d168633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76229 q = 1) (hb : d168636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35658 q ha hb
    | true =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167673 q = 1) (hb : d168637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167674 q = 1) (hb : d168638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167675 q = 1) (hb : d168639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167680 q = 1) (hb : d168644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167680, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167680, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167681 q = 1) (hb : d168645 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167681, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167681, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167682 q = 1) (hb : d168646 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167682, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167682, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35662 (p : Pattern) (ha : d167688 p = 1) (hb : d168652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167678 q = 1) (hb : d168642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167678, d168642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35660 q ha hb
    | true =>
      simp only [d167678, d168642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167679 q = 1) (hb : d168643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167679, d168643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167679, d168643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167683 q = 1) (hb : d168647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167683, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35661 q ha hb
    | true =>
      simp only [d167683, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167684 q = 1) (hb : d168648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167684, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167684, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167685 q = 1) (hb : d168649 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167685, d168649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167685, d168649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167686 q = 1) (hb : d168650 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167686, d168650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167686, d168650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167687 q = 1) (hb : d168651 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167687, d168651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167687, d168651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167688 q = 1) (hb : d168652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167688, d168652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167688, d168652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35663 (p : Pattern) (ha : d167692 p = 1) (hb : d168660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167683 q = 1) (hb : d168647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167683, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35661 q ha hb
    | true =>
      simp only [d167683, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167684 q = 1) (hb : d168648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167684, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167684, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137730 q = 1) (hb : d168655 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35619 q ha hb
    | true =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137731 q = 1) (hb : d168656 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167689 q = 1) (hb : d168657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167689, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167689, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167690 q = 1) (hb : d168658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167690, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167690, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167691 q = 1) (hb : d168659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167691, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167691, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167692 q = 1) (hb : d168660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167692, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167692, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35664 (p : Pattern) (ha : d167695 p = 1) (hb : d168646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53198 q = 1) (hb : d168631 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35657 q ha hb
    | true =>
      simp only [d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137709 q = 1) (hb : d168632 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137710 q = 1) (hb : d168633 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76229 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76229 q = 1) (hb : d168636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35658 q ha hb
    | true =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167673 q = 1) (hb : d168637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167673, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167674 q = 1) (hb : d168638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167674, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167675 q = 1) (hb : d168639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167675, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53203 q = 1) (hb : d168636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35618 q ha hb
    | true =>
      simp only [d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137712 q = 1) (hb : d168637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137713 q = 1) (hb : d168638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137719 q = 1) (hb : d168644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137719, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137719, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167694 q = 1) (hb : d168645 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167694, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167694, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167695 q = 1) (hb : d168646 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167695, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167695, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35665 (p : Pattern) (ha : d167707 p = 1) (hb : d168666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167696 q = 1) (hb : d168647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167696, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35664 q ha hb
    | true =>
      simp only [d167696, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167697 q = 1) (hb : d168648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167697, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167697, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167704 q = 1) (hb : d168663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167704, d168663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167704, d168663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167705 q = 1) (hb : d168664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167705, d168664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167705, d168664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167706 q = 1) (hb : d168665 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167706, d168665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167706, d168665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167707 q = 1) (hb : d168666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167707, d168666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167707, d168666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35666 (p : Pattern) (ha : d167713 p = 1) (hb : d168672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167693 q = 1) (hb : d168661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167693, d168661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35662 q ha hb
    | true =>
      simp only [d167693, d168661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35663 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167703 q = 1) (hb : d168662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167703, d168662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167703, d168662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167708 q = 1) (hb : d168667 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167708, d168667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35665 q ha hb
    | true =>
      simp only [d167708, d168667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167709 q = 1) (hb : d168668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167709, d168668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167709, d168668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167710 q = 1) (hb : d168669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167710, d168669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167710, d168669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167711 q = 1) (hb : d168670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167711, d168670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167711, d168670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167712 q = 1) (hb : d168671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167712, d168671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167712, d168671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167713 q = 1) (hb : d168672 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167713, d168672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167713, d168672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35667 (p : Pattern) (ha : d167719 p = 1) (hb : d168689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167575 q = 1) (hb : d168523 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167575, d168523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167575, d168523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35629 q ha hb
  have h2 (q : Pattern) (ha : d167576 q = 1) (hb : d168524 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167576, d168524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167576, d168524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167584 q = 1) (hb : d168533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167584, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35629 q ha hb
    | true =>
      simp only [d167584, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35631 q ha hb
  have h4 (q : Pattern) (ha : d167585 q = 1) (hb : d168534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167585, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167585, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167586 q = 1) (hb : d168535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167586, d168535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167586, d168535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167651 q = 1) (hb : d168599 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167651, d168599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35645 q ha hb
    | true =>
      simp only [d167651, d168599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35653 q ha hb
  have h7 (q : Pattern) (ha : d167658 q = 1) (hb : d168612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167658, d168612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35654 q ha hb
    | true =>
      simp only [d167658, d168612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35616 q ha hb
  have h8 (q : Pattern) (ha : d167659 q = 1) (hb : d168613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167659, d168613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167659, d168613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167660 q = 1) (hb : d168614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167660, d168614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167660, d168614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d167661 q = 1) (hb : d168615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167661, d168615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167661, d168615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167665 q = 1) (hb : d168619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167665, d168619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167665, d168619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35655 q ha hb
  have h12 (q : Pattern) (ha : d137702 q = 1) (hb : d168621 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137702, d168621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137702, d168621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35617 q ha hb
  have h13 (q : Pattern) (ha : d167666 q = 1) (hb : d168622 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167666, d168622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167666, d168622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167667 q = 1) (hb : d168623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167667, d168623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167667, d168623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167668 q = 1) (hb : d168624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167668, d168624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d167668, d168624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d167669 q = 1) (hb : d168625 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167669, d168625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167669, d168625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167714 q = 1) (hb : d168673 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167714, d168673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167714, d168673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35666 q ha hb
  have h18 (q : Pattern) (ha : d137767 q = 1) (hb : d168684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137767, d168684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137767, d168684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35621 q ha hb
  have h19 (q : Pattern) (ha : d167715 q = 1) (hb : d168685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167715, d168685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167715, d168685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167716 q = 1) (hb : d168686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167716, d168686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167716, d168686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d167717 q = 1) (hb : d168687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167717, d168687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d167717, d168687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d167718 q = 1) (hb : d168688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167718, d168688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167718, d168688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167719 q = 1) (hb : d168689 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167719, d168689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167719, d168689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35668 (p : Pattern) (ha : d167725 p = 1) (hb : d168695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167720 q = 1) (hb : d168690 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167720, d168690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167720, d168690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35667 q ha hb
  have h2 (q : Pattern) (ha : d167721 q = 1) (hb : d168691 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167721, d168691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167721, d168691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167722 q = 1) (hb : d168692 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167722, d168692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167722, d168692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167723 q = 1) (hb : d168693 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167723, d168693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167723, d168693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167724 q = 1) (hb : d168694 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167724, d168694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167724, d168694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167725 q = 1) (hb : d168695 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167725, d168695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167725, d168695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35669 (p : Pattern) (ha : d10370 p = 1) (hb : d53343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5716 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5717 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5717, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d5238 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5239 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5239, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d5243 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5243, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d5244 q = 1) (hb : d53341 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5244, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5245 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5245, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d10370 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10370, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10370, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35670 (p : Pattern) (ha : d53350 p = 1) (hb : d168704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35669 q ha hb
    | true =>
      simp only [d10371, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15550 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15550, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53350 q = 1) (hb : d168704 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35671 (p : Pattern) (ha : d137794 p = 1) (hb : d168715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53350 q = 1) (hb : d168705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35670 q ha hb
    | true =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137785 q = 1) (hb : d168706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137786 q = 1) (hb : d168707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137788 q = 1) (hb : d168709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137788, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137788, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137793 q = 1) (hb : d168714 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137793, d168714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137793, d168714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137794 q = 1) (hb : d168715 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137794, d168715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137794, d168715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35672 (p : Pattern) (ha : d137804 p = 1) (hb : d168725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d168723 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137803 q = 1) (hb : d168724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137803, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137803, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137804 q = 1) (hb : d168725 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137804, d168725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137804, d168725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35673 (p : Pattern) (ha : d137814 p = 1) (hb : d168735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d168723 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137803 q = 1) (hb : d168724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137803, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137803, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137814 q = 1) (hb : d168735 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137814, d168735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137814, d168735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35674 (p : Pattern) (ha : d137904 p = 1) (hb : d168816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137893 q = 1) (hb : d168805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137893, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
    | true =>
      simp only [d137893, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137894 q = 1) (hb : d168806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137894, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137894, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137895 q = 1) (hb : d168807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137895, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137895, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137896 q = 1) (hb : d168808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137896, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137896, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137897 q = 1) (hb : d168809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137897, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137897, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137899 q = 1) (hb : d168811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137899, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35673 q ha hb
    | true =>
      simp only [d137899, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137900 q = 1) (hb : d168812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137900, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137900, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137901 q = 1) (hb : d168813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137901, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137901, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137902 q = 1) (hb : d168814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137902, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137902, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137903 q = 1) (hb : d168815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137903, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137903, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137904 q = 1) (hb : d168816 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137904, d168816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137904, d168816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35675 (p : Pattern) (ha : d137913 p = 1) (hb : d168825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137899 q = 1) (hb : d168811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137899, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35673 q ha hb
    | true =>
      simp only [d137899, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137900 q = 1) (hb : d168812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137900, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137900, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137901 q = 1) (hb : d168813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137901, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137901, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137902 q = 1) (hb : d168814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137902, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137902, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137903 q = 1) (hb : d168815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137903, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137903, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137913 q = 1) (hb : d168825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137913, d168825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137913, d168825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35676 (p : Pattern) (ha : d53520 p = 1) (hb : d168836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35669 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35669 q ha hb
    | true =>
      simp only [d10371, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15779 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15779, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d53520 q = 1) (hb : d168836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35677 (p : Pattern) (ha : d137941 p = 1) (hb : d168855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53520 q = 1) (hb : d168837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35676 q ha hb
    | true =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137924 q = 1) (hb : d168838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137925 q = 1) (hb : d168839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137931 q = 1) (hb : d168845 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137931, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137931, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137940 q = 1) (hb : d168854 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137940, d168854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137940, d168854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137941 q = 1) (hb : d168855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137941, d168855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137941, d168855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro35678 (p : Pattern) (ha : d137952 p = 1) (hb : d168878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137942 q = 1) (hb : d168856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35677 q ha hb
    | true =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137943 q = 1) (hb : d168857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137949 q = 1) (hb : d168875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137949, d168875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137949, d168875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137950 q = 1) (hb : d168876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137950, d168876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137950, d168876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137951 q = 1) (hb : d168877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137951, d168877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137951, d168877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137952 q = 1) (hb : d168878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137952, d168878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137952, d168878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35679 (p : Pattern) (ha : d137978 p = 1) (hb : d168884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137973 q = 1) (hb : d168879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137973, d168879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35678 q ha hb
    | true =>
      simp only [d137973, d168879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137974 q = 1) (hb : d168880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137974, d168880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137974, d168880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137975 q = 1) (hb : d168881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137975, d168881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137975, d168881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137976 q = 1) (hb : d168882 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137976, d168882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137976, d168882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137977 q = 1) (hb : d168883 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137977, d168883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137977, d168883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137978 q = 1) (hb : d168884 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137978, d168884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137978, d168884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35680 (p : Pattern) (ha : d10352 p = 1) (hb : d53331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10349 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10349, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10350 q = 1) (hb : d53311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10350, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10351 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10351, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10352 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10352, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10352, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35681 (p : Pattern) (ha : d53348 p = 1) (hb : d168700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13675, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15545 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15545, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53348 q = 1) (hb : d168700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35682 (p : Pattern) (ha : d10370 p = 1) (hb : d69330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d69324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5715, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5716 q = 1) (hb : d69325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5717 q = 1) (hb : d69326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5717, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h10 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d5243 q = 1) (hb : d69327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d5244 q = 1) (hb : d69328 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5245 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d10370 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10370, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10370, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro35683 (p : Pattern) (ha : d69335 p = 1) (hb : d168704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35682 q ha hb
    | true =>
      simp only [d10371, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d69333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d69334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15550 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15550, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d69335 q = 1) (hb : d168704 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35684 (p : Pattern) (ha : d167734 p = 1) (hb : d168711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53348 q = 1) (hb : d168701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35681 q ha hb
    | true =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137783 q = 1) (hb : d168702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137784 q = 1) (hb : d168703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69335 q = 1) (hb : d168705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35683 q ha hb
    | true =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167730 q = 1) (hb : d168706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167731 q = 1) (hb : d168707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167732 q = 1) (hb : d168708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53350 q = 1) (hb : d168705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35670 q ha hb
    | true =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137785 q = 1) (hb : d168706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137786 q = 1) (hb : d168707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137788 q = 1) (hb : d168709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137788, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137788, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167733 q = 1) (hb : d168710 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167733, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167733, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167734 q = 1) (hb : d168711 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167734, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167734, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35685 (p : Pattern) (ha : d167740 p = 1) (hb : d168721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167738 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167739 q = 1) (hb : d168720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167739, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167739, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167740 q = 1) (hb : d168721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167740, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167740, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35686 (p : Pattern) (ha : d167746 p = 1) (hb : d168731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167741 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35685 q ha hb
    | true =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
  have h2 (q : Pattern) (ha : d167742 q = 1) (hb : d168727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167742, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167742, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167743 q = 1) (hb : d168728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167743, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167743, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167744 q = 1) (hb : d168729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167744, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167744, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167745 q = 1) (hb : d168730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167745, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167745, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167746 q = 1) (hb : d168731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167746, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167746, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35687 (p : Pattern) (ha : d167749 p = 1) (hb : d168734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167738 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167739 q = 1) (hb : d168720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167739, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167739, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167749 q = 1) (hb : d168734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167749, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167749, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35688 (p : Pattern) (ha : d167755 p = 1) (hb : d168741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167741 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35685 q ha hb
    | true =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
  have h2 (q : Pattern) (ha : d167742 q = 1) (hb : d168727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167742, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167742, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167743 q = 1) (hb : d168728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167743, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167743, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167744 q = 1) (hb : d168729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167744, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167744, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167745 q = 1) (hb : d168730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167745, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167745, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167750 q = 1) (hb : d168736 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35687 q ha hb
    | true =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35673 q ha hb
  have h7 (q : Pattern) (ha : d167751 q = 1) (hb : d168737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167751, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167751, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167752 q = 1) (hb : d168738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167752, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167752, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d167753 q = 1) (hb : d168739 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167753, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167753, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167754 q = 1) (hb : d168740 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167754, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167754, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167755 q = 1) (hb : d168741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167755, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167755, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35689 (p : Pattern) (ha : d137827 p = 1) (hb : d168748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d168723 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137826 q = 1) (hb : d168747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137826, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137826, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137827 q = 1) (hb : d168748 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137827, d168748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137827, d168748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35690 (p : Pattern) (ha : d137837 p = 1) (hb : d168758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137835 q = 1) (hb : d168756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137835, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137835, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137836 q = 1) (hb : d168757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137836, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137836, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137837 q = 1) (hb : d168758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137837, d168758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137837, d168758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35691 (p : Pattern) (ha : d167760 p = 1) (hb : d168746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167738 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167759 q = 1) (hb : d168745 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167759, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167759, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167760 q = 1) (hb : d168746 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167760, d168746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167760, d168746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35692 (p : Pattern) (ha : d167767 p = 1) (hb : d168755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167765 q = 1) (hb : d168753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167765, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167765, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167766 q = 1) (hb : d168754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167766, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167766, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167767 q = 1) (hb : d168755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167767, d168755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167767, d168755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35693 (p : Pattern) (ha : d113872 p = 1) (hb : d168700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15545 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113872 q = 1) (hb : d168700 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35694 (p : Pattern) (ha : d167775 p = 1) (hb : d168764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113872 q = 1) (hb : d168701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35693 q ha hb
    | true =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167771 q = 1) (hb : d168702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167771, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167771, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167772 q = 1) (hb : d168703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167772, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167772, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167773 q = 1) (hb : d168762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167773, d168762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167773, d168762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53348 q = 1) (hb : d168701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35681 q ha hb
    | true =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d137783 q = 1) (hb : d168702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137784 q = 1) (hb : d168703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d69335 q = 1) (hb : d168705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35683 q ha hb
    | true =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d167730 q = 1) (hb : d168706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167731 q = 1) (hb : d168707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167732 q = 1) (hb : d168708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167774 q = 1) (hb : d168763 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167774, d168763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167774, d168763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167775 q = 1) (hb : d168764 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167775, d168764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167775, d168764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h17 p ha hb
theorem andIntro35695 (p : Pattern) (ha : d167780 p = 1) (hb : d168711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53348 q = 1) (hb : d168701 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35681 q ha hb
    | true =>
      simp only [d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137783 q = 1) (hb : d168702 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137783, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137784 q = 1) (hb : d168703 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137784, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69335 q = 1) (hb : d168705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35683 q ha hb
    | true =>
      simp only [d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167730 q = 1) (hb : d168706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167730, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167731 q = 1) (hb : d168707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167731, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167732 q = 1) (hb : d168708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167732, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167778 q = 1) (hb : d168709 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167778, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167778, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167779 q = 1) (hb : d168710 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167779, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167779, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167780 q = 1) (hb : d168711 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167780, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167780, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35696 (p : Pattern) (ha : d167786 p = 1) (hb : d168770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167776 q = 1) (hb : d168765 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167776, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35694 q ha hb
    | true =>
      simp only [d167776, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167777 q = 1) (hb : d168766 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167777, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167777, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167781 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35695 q ha hb
    | true =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167782 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167783 q = 1) (hb : d168767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167783, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167783, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167784 q = 1) (hb : d168768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167784, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167784, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167785 q = 1) (hb : d168769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167785, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167785, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167786 q = 1) (hb : d168770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167786, d168770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167786, d168770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35697 (p : Pattern) (ha : d167790 p = 1) (hb : d168721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167781 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35695 q ha hb
    | true =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167782 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167787 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167787, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167787, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167788 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167788, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167788, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167789 q = 1) (hb : d168720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167789, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167789, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167790 q = 1) (hb : d168721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167790, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167790, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35698 (p : Pattern) (ha : d167796 p = 1) (hb : d168776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167793 q = 1) (hb : d168773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167793, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167793, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167794 q = 1) (hb : d168774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167794, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167794, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167795 q = 1) (hb : d168775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167795, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167795, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167796 q = 1) (hb : d168776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167796, d168776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167796, d168776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35699 (p : Pattern) (ha : d167802 p = 1) (hb : d168782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167761 q = 1) (hb : d168749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167761, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35691 q ha hb
    | true =>
      simp only [d167761, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35689 q ha hb
  have h2 (q : Pattern) (ha : d167762 q = 1) (hb : d168750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167762, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167762, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167763 q = 1) (hb : d168751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167763, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167763, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167764 q = 1) (hb : d168752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167764, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167764, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167768 q = 1) (hb : d168759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167768, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35692 q ha hb
    | true =>
      simp only [d167768, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35690 q ha hb
  have h6 (q : Pattern) (ha : d167769 q = 1) (hb : d168760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167769, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167769, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167770 q = 1) (hb : d168761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167770, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167770, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167791 q = 1) (hb : d168771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167791, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35696 q ha hb
    | true =>
      simp only [d167791, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35697 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167741 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167792 q = 1) (hb : d168772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167792, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167792, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167797 q = 1) (hb : d168777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167797, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35698 q ha hb
    | true =>
      simp only [d167797, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167798 q = 1) (hb : d168778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167798, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167798, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167799 q = 1) (hb : d168779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167799, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167799, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167800 q = 1) (hb : d168780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167800, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167800, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167801 q = 1) (hb : d168781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167801, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167801, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167802 q = 1) (hb : d168782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167802, d168782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167802, d168782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35700 (p : Pattern) (ha : d137872 p = 1) (hb : d168784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d168723 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137826 q = 1) (hb : d168747 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137826, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137826, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137872 q = 1) (hb : d168784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137872, d168784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137872, d168784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35701 (p : Pattern) (ha : d137878 p = 1) (hb : d168790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d168722 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137835 q = 1) (hb : d168756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137835, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137835, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137836 q = 1) (hb : d168757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137836, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137836, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137878 q = 1) (hb : d168790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137878, d168790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137878, d168790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35702 (p : Pattern) (ha : d167803 p = 1) (hb : d168783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167738 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167738, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167759 q = 1) (hb : d168745 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167759, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167759, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167803 q = 1) (hb : d168783 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167803, d168783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167803, d168783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35703 (p : Pattern) (ha : d167808 p = 1) (hb : d168789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167737 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167737, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167765 q = 1) (hb : d168753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167765, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167765, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167766 q = 1) (hb : d168754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167766, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167766, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167808 q = 1) (hb : d168789 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167808, d168789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167808, d168789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35704 (p : Pattern) (ha : d167812 p = 1) (hb : d168794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167776 q = 1) (hb : d168765 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167776, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35694 q ha hb
    | true =>
      simp only [d167776, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167777 q = 1) (hb : d168766 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167777, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167777, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167781 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35695 q ha hb
    | true =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167782 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167783 q = 1) (hb : d168767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167783, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167783, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167784 q = 1) (hb : d168768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167784, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167784, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167785 q = 1) (hb : d168769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167785, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167785, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167812 q = 1) (hb : d168794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167812, d168794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167812, d168794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35705 (p : Pattern) (ha : d167813 p = 1) (hb : d168734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167781 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35695 q ha hb
    | true =>
      simp only [d167781, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167782 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167782, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d168716 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35671 q ha hb
    | true =>
      simp only [d137795, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d168717 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167787 q = 1) (hb : d168718 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167787, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167787, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167788 q = 1) (hb : d168719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167788, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167788, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167789 q = 1) (hb : d168720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167789, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167789, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167813 q = 1) (hb : d168734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167813, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167813, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35706 (p : Pattern) (ha : d167816 p = 1) (hb : d168797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167735 q = 1) (hb : d168712 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35684 q ha hb
    | true =>
      simp only [d167735, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167736 q = 1) (hb : d168713 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167736, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167793 q = 1) (hb : d168773 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167793, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167793, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167794 q = 1) (hb : d168774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167794, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167794, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167795 q = 1) (hb : d168775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167795, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167795, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167816 q = 1) (hb : d168797 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167816, d168797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167816, d168797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35707 (p : Pattern) (ha : d167822 p = 1) (hb : d168803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167761 q = 1) (hb : d168749 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167761, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35691 q ha hb
    | true =>
      simp only [d167761, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35689 q ha hb
  have h2 (q : Pattern) (ha : d167762 q = 1) (hb : d168750 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167762, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167762, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167763 q = 1) (hb : d168751 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167763, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167763, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167764 q = 1) (hb : d168752 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167764, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167764, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167768 q = 1) (hb : d168759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167768, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35692 q ha hb
    | true =>
      simp only [d167768, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35690 q ha hb
  have h6 (q : Pattern) (ha : d167769 q = 1) (hb : d168760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167769, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167769, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167770 q = 1) (hb : d168761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167770, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167770, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167791 q = 1) (hb : d168771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167791, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35696 q ha hb
    | true =>
      simp only [d167791, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35697 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167741 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167792 q = 1) (hb : d168772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167792, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167792, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d167797 q = 1) (hb : d168777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167797, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35698 q ha hb
    | true =>
      simp only [d167797, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d167798 q = 1) (hb : d168778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167798, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167798, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167799 q = 1) (hb : d168779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167799, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167799, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167800 q = 1) (hb : d168780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167800, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167800, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167801 q = 1) (hb : d168781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167801, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167801, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167804 q = 1) (hb : d168785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167804, d168785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35702 q ha hb
    | true =>
      simp only [d167804, d168785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35700 q ha hb
  have h17 (q : Pattern) (ha : d167805 q = 1) (hb : d168786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167805, d168786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167805, d168786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167806 q = 1) (hb : d168787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167806, d168787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167806, d168787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d167807 q = 1) (hb : d168788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167807, d168788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167807, d168788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167809 q = 1) (hb : d168791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167809, d168791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35703 q ha hb
    | true =>
      simp only [d167809, d168791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35701 q ha hb
  have h21 (q : Pattern) (ha : d167810 q = 1) (hb : d168792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167810, d168792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167810, d168792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d167811 q = 1) (hb : d168793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167811, d168793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167811, d168793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167814 q = 1) (hb : d168795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167814, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35704 q ha hb
    | true =>
      simp only [d167814, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35705 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d167750 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d167815 q = 1) (hb : d168796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167815, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d167815, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d167817 q = 1) (hb : d168798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167817, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35706 q ha hb
    | true =>
      simp only [d167817, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d167818 q = 1) (hb : d168799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167818, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d167818, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d167819 q = 1) (hb : d168800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167819, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d167819, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d167820 q = 1) (hb : d168801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167820, d168801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d167820, d168801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d167821 q = 1) (hb : d168802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167821, d168802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167821, d168802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d167822 q = 1) (hb : d168803 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167822, d168803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167822, d168803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35708 (p : Pattern) (ha : d167829 p = 1) (hb : d168810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167824 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167824, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35697 q ha hb
    | true =>
      simp only [d167824, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
  have h2 (q : Pattern) (ha : d167825 q = 1) (hb : d168727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167825, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167825, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167826 q = 1) (hb : d168728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167826, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167826, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167827 q = 1) (hb : d168729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167827, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167827, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167828 q = 1) (hb : d168730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167828, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167828, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137893 q = 1) (hb : d168805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137893, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
    | true =>
      simp only [d137893, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137894 q = 1) (hb : d168806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137894, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137894, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137895 q = 1) (hb : d168807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137895, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137895, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137896 q = 1) (hb : d168808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137896, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137896, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137897 q = 1) (hb : d168809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137897, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137897, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167829 q = 1) (hb : d168810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167829, d168810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167829, d168810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35709 (p : Pattern) (ha : d167836 p = 1) (hb : d168823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167814 q = 1) (hb : d168795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167814, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35704 q ha hb
    | true =>
      simp only [d167814, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35705 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167815 q = 1) (hb : d168796 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167815, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167815, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167817 q = 1) (hb : d168798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167817, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35706 q ha hb
    | true =>
      simp only [d167817, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167818 q = 1) (hb : d168799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167818, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167818, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167819 q = 1) (hb : d168800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167819, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167819, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167834 q = 1) (hb : d168821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167834, d168821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167834, d168821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167835 q = 1) (hb : d168822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167835, d168822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167835, d168822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167836 q = 1) (hb : d168823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167836, d168823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167836, d168823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35710 (p : Pattern) (ha : d53515 p = 1) (hb : d168831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13813, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35680 q ha hb
    | true =>
      simp only [d10353, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13816 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15770 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15770, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53515 q = 1) (hb : d168831 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35711 (p : Pattern) (ha : d76365 p = 1) (hb : d168836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35682 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35682 q ha hb
    | true =>
      simp only [d10371, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d15779 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15779, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d76365 q = 1) (hb : d168836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35712 (p : Pattern) (ha : d113973 p = 1) (hb : d168831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15770 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113973 q = 1) (hb : d168831 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35713 (p : Pattern) (ha : d167849 p = 1) (hb : d168842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137920 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113973 q = 1) (hb : d168832 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35712 q ha hb
    | true =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167842 q = 1) (hb : d168833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167842, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167842, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167843 q = 1) (hb : d168834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167843, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167843, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167844 q = 1) (hb : d168835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167844, d168835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167844, d168835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53515 q = 1) (hb : d168832 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35710 q ha hb
    | true =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d137921 q = 1) (hb : d168833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137922 q = 1) (hb : d168834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d76365 q = 1) (hb : d168837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35711 q ha hb
    | true =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d167845 q = 1) (hb : d168838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167846 q = 1) (hb : d168839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167847 q = 1) (hb : d168840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167848 q = 1) (hb : d168841 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167848, d168841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167848, d168841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167849 q = 1) (hb : d168842 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167849, d168842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167849, d168842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h17 p ha hb
theorem andIntro35714 (p : Pattern) (ha : d167854 p = 1) (hb : d168847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53515 q = 1) (hb : d168832 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35710 q ha hb
    | true =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137921 q = 1) (hb : d168833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137922 q = 1) (hb : d168834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76365 q = 1) (hb : d168837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35711 q ha hb
    | true =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167845 q = 1) (hb : d168838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167846 q = 1) (hb : d168839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167847 q = 1) (hb : d168840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167852 q = 1) (hb : d168845 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167852, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167852, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d167853 q = 1) (hb : d168846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167853, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167853, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d167854 q = 1) (hb : d168847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167854, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167854, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35715 (p : Pattern) (ha : d167860 p = 1) (hb : d168853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167850 q = 1) (hb : d168843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167850, d168843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35713 q ha hb
    | true =>
      simp only [d167850, d168843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167851 q = 1) (hb : d168844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167851, d168844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167851, d168844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167855 q = 1) (hb : d168848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167855, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35714 q ha hb
    | true =>
      simp only [d167855, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167856 q = 1) (hb : d168849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167856, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167856, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167857 q = 1) (hb : d168850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167857, d168850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167857, d168850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167858 q = 1) (hb : d168851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167858, d168851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167858, d168851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167859 q = 1) (hb : d168852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167859, d168852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167859, d168852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167860 q = 1) (hb : d168853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167860, d168853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167860, d168853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35716 (p : Pattern) (ha : d167864 p = 1) (hb : d168861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167855 q = 1) (hb : d168848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167855, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35714 q ha hb
    | true =>
      simp only [d167855, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167856 q = 1) (hb : d168849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167856, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167856, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137942 q = 1) (hb : d168856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35677 q ha hb
    | true =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137943 q = 1) (hb : d168857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167861 q = 1) (hb : d168858 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167861, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167861, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167862 q = 1) (hb : d168859 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167862, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167862, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167863 q = 1) (hb : d168860 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167863, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167863, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167864 q = 1) (hb : d168861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167864, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167864, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35717 (p : Pattern) (ha : d167867 p = 1) (hb : d168847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53515 q = 1) (hb : d168832 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35710 q ha hb
    | true =>
      simp only [d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137921 q = 1) (hb : d168833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137921, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137922 q = 1) (hb : d168834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137922, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76365 q = 1) (hb : d168837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35711 q ha hb
    | true =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167845 q = 1) (hb : d168838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167845, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167846 q = 1) (hb : d168839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167846, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167847 q = 1) (hb : d168840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167847, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53520 q = 1) (hb : d168837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35676 q ha hb
    | true =>
      simp only [d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d137924 q = 1) (hb : d168838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137925 q = 1) (hb : d168839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137931 q = 1) (hb : d168845 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137931, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137931, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167866 q = 1) (hb : d168846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167866, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167866, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167867 q = 1) (hb : d168847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167867, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167867, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35718 (p : Pattern) (ha : d167879 p = 1) (hb : d168867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167868 q = 1) (hb : d168848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167868, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35717 q ha hb
    | true =>
      simp only [d167868, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167869 q = 1) (hb : d168849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167869, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167869, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167876 q = 1) (hb : d168864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167876, d168864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167876, d168864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167877 q = 1) (hb : d168865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167877, d168865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167877, d168865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167878 q = 1) (hb : d168866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167878, d168866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167878, d168866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167879 q = 1) (hb : d168867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167879, d168867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167879, d168867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35719 (p : Pattern) (ha : d167885 p = 1) (hb : d168873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167865 q = 1) (hb : d168862 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167865, d168862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35715 q ha hb
    | true =>
      simp only [d167865, d168862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35716 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167874 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167875 q = 1) (hb : d168863 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167875, d168863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167875, d168863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d167880 q = 1) (hb : d168868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167880, d168868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35718 q ha hb
    | true =>
      simp only [d167880, d168868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167881 q = 1) (hb : d168869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167881, d168869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167881, d168869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167882 q = 1) (hb : d168870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167882, d168870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167882, d168870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167883 q = 1) (hb : d168871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167883, d168871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167883, d168871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167884 q = 1) (hb : d168872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167884, d168872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167884, d168872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167885 q = 1) (hb : d168873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167885, d168873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167885, d168873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35720 (p : Pattern) (ha : d167891 p = 1) (hb : d168890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167747 q = 1) (hb : d168732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167747, d168732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167747, d168732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35686 q ha hb
  have h2 (q : Pattern) (ha : d167748 q = 1) (hb : d168733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167748, d168733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167748, d168733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167756 q = 1) (hb : d168742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167756, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35686 q ha hb
    | true =>
      simp only [d167756, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35688 q ha hb
  have h4 (q : Pattern) (ha : d167757 q = 1) (hb : d168743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167757, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167757, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167758 q = 1) (hb : d168744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167758, d168744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167758, d168744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167823 q = 1) (hb : d168804 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167823, d168804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35699 q ha hb
    | true =>
      simp only [d167823, d168804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35707 q ha hb
  have h7 (q : Pattern) (ha : d167830 q = 1) (hb : d168817 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167830, d168817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35708 q ha hb
    | true =>
      simp only [d167830, d168817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35674 q ha hb
  have h8 (q : Pattern) (ha : d167831 q = 1) (hb : d168818 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167831, d168818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167831, d168818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167832 q = 1) (hb : d168819 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167832, d168819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167832, d168819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d167833 q = 1) (hb : d168820 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167833, d168820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167833, d168820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167837 q = 1) (hb : d168824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167837, d168824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167837, d168824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35709 q ha hb
  have h12 (q : Pattern) (ha : d137914 q = 1) (hb : d168826 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137914, d168826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137914, d168826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35675 q ha hb
  have h13 (q : Pattern) (ha : d167838 q = 1) (hb : d168827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167838, d168827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d167838, d168827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167839 q = 1) (hb : d168828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167839, d168828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167839, d168828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d167840 q = 1) (hb : d168829 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167840, d168829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d167840, d168829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d167841 q = 1) (hb : d168830 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167841, d168830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167841, d168830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167886 q = 1) (hb : d168874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167886, d168874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167886, d168874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35719 q ha hb
  have h18 (q : Pattern) (ha : d137979 q = 1) (hb : d168885 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137979, d168885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137979, d168885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35679 q ha hb
  have h19 (q : Pattern) (ha : d167887 q = 1) (hb : d168886 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167887, d168886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167887, d168886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167888 q = 1) (hb : d168887 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167888, d168887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167888, d168887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d167889 q = 1) (hb : d168888 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167889, d168888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d167889, d168888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d167890 q = 1) (hb : d168889 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167890, d168889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d167890, d168889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167891 q = 1) (hb : d168890 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167891, d168890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167891, d168890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35721 (p : Pattern) (ha : d167897 p = 1) (hb : d168896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167892 q = 1) (hb : d168891 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167892, d168891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167892, d168891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35720 q ha hb
  have h2 (q : Pattern) (ha : d167893 q = 1) (hb : d168892 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167893, d168892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167893, d168892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167894 q = 1) (hb : d168893 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167894, d168893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167894, d168893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167895 q = 1) (hb : d168894 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167895, d168894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167895, d168894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167896 q = 1) (hb : d168895 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167896, d168895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167896, d168895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167897 q = 1) (hb : d168896 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167897, d168896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167897, d168896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35722 (p : Pattern) (ha : d167903 p = 1) (hb : d168902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d167304 q = 1) (hb : d168137 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167304, d168137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35474 q ha hb
    | true =>
      simp only [d167304, d168137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35503 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167385 q = 1) (hb : d168281 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167385, d168281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167385, d168281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35551 q ha hb
  have h3 (q : Pattern) (ha : d167386 q = 1) (hb : d168282 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167386, d168282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d167386, d168282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167555 q = 1) (hb : d168488 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167555, d168488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167555, d168488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35609 q ha hb
  have h5 (q : Pattern) (ha : d167556 q = 1) (hb : d168489 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167556, d168489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167556, d168489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167557 q = 1) (hb : d168490 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167557, d168490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167557, d168490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167726 q = 1) (hb : d168696 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167726, d168696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167726, d168696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35668 q ha hb
  have h8 (q : Pattern) (ha : d167727 q = 1) (hb : d168697 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167727, d168697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167727, d168697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167728 q = 1) (hb : d168698 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167728, d168698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167728, d168698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167729 q = 1) (hb : d168699 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167729, d168699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167729, d168699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167898 q = 1) (hb : d168897 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167898, d168897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167898, d168897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35721 q ha hb
  have h12 (q : Pattern) (ha : d167899 q = 1) (hb : d168898 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167899, d168898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167899, d168898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167900 q = 1) (hb : d168899 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167900, d168899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167900, d168899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167901 q = 1) (hb : d168900 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167901, d168900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167901, d168900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167902 q = 1) (hb : d168901 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d167902, d168901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167902, d168901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167903 q = 1) (hb : d168902 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d167903, d168902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167903, d168902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro35723 (p : Pattern) (ha : d167909 p = 1) (hb : d168908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167904 q = 1) (hb : d168903 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d167904, d168903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35722 q ha hb
    | true =>
      simp only [d167904, d168903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167905 q = 1) (hb : d168904 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d167905, d168904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167905, d168904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167906 q = 1) (hb : d168905 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d167906, d168905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167906, d168905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167907 q = 1) (hb : d168906 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d167907, d168906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167907, d168906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167908 q = 1) (hb : d168907 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d167908, d168907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167908, d168907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167909 q = 1) (hb : d168908 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d167909, d168908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167909, d168908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35724 (p : Pattern) (ha : d167915 p = 1) (hb : d168914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167910 q = 1) (hb : d168909 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d167910, d168909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35723 q ha hb
    | true =>
      simp only [d167910, d168909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167911 q = 1) (hb : d168910 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d167911, d168910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167911, d168910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167912 q = 1) (hb : d168911 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d167912, d168911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167912, d168911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167913 q = 1) (hb : d168912 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d167913, d168912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167913, d168912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167914 q = 1) (hb : d168913 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d167914, d168913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167914, d168913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167915 q = 1) (hb : d168914 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d167915, d168914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167915, d168914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35725 (p : Pattern) (ha : d167921 p = 1) (hb : d168920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167916 q = 1) (hb : d168915 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d167916, d168915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35724 q ha hb
    | true =>
      simp only [d167916, d168915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167917 q = 1) (hb : d168916 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d167917, d168916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167917, d168916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167918 q = 1) (hb : d168917 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d167918, d168917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167918, d168917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167919 q = 1) (hb : d168918 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d167919, d168918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167919, d168918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167920 q = 1) (hb : d168919 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d167920, d168919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167920, d168919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167921 q = 1) (hb : d168920 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d167921, d168920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167921, d168920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35726 (p : Pattern) (ha : d167927 p = 1) (hb : d168926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167922 q = 1) (hb : d168921 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d167922, d168921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35725 q ha hb
    | true =>
      simp only [d167922, d168921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167923 q = 1) (hb : d168922 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d167923, d168922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167923, d168922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167924 q = 1) (hb : d168923 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d167924, d168923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167924, d168923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167925 q = 1) (hb : d168924 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d167925, d168924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167925, d168924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167926 q = 1) (hb : d168925 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d167926, d168925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167926, d168925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167927 q = 1) (hb : d168926 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d167927, d168926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167927, d168926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35727 (p : Pattern) (ha : d167933 p = 1) (hb : d168932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167928 q = 1) (hb : d168927 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d167928, d168927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35726 q ha hb
    | true =>
      simp only [d167928, d168927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167929 q = 1) (hb : d168928 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d167929, d168928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167929, d168928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167930 q = 1) (hb : d168929 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d167930, d168929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167930, d168929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167931 q = 1) (hb : d168930 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d167931, d168930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167931, d168930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167932 q = 1) (hb : d168931 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d167932, d168931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167932, d168931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167933 q = 1) (hb : d168932 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d167933, d168932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167933, d168932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35728 (p : Pattern) (ha : d167939 p = 1) (hb : d168938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167934 q = 1) (hb : d168933 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d167934, d168933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35727 q ha hb
    | true =>
      simp only [d167934, d168933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167935 q = 1) (hb : d168934 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d167935, d168934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167935, d168934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167936 q = 1) (hb : d168935 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d167936, d168935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167936, d168935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167937 q = 1) (hb : d168936 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d167937, d168936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167937, d168936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167938 q = 1) (hb : d168937 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d167938, d168937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167938, d168937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167939 q = 1) (hb : d168938 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d167939, d168938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167939, d168938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35729 (p : Pattern) (ha : d167945 p = 1) (hb : d168944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167940 q = 1) (hb : d168939 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d167940, d168939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35728 q ha hb
    | true =>
      simp only [d167940, d168939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167941 q = 1) (hb : d168940 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d167941, d168940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167941, d168940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167942 q = 1) (hb : d168941 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d167942, d168941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167942, d168941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167943 q = 1) (hb : d168942 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d167943, d168942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167943, d168942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167944 q = 1) (hb : d168943 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d167944, d168943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167944, d168943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167945 q = 1) (hb : d168944 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d167945, d168944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167945, d168944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35730 (p : Pattern) (ha : d142666 p = 1) (hb : d163447 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d142666 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35174 q ha hb
    | true =>
      simp only [d14001, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26357 q ha hb
  have h2 (q : Pattern) (ha : d14057 q = 1) (hb : d142666 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14058 q = 1) (hb : d142666 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14058, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14059 q = 1) (hb : d142666 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14060 q = 1) (hb : d142666 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163447 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163447, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163447, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35731 (p : Pattern) (ha : d142666 p = 1) (hb : d163457 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d142666 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35179 q ha hb
    | true =>
      simp only [d14033, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26362 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163453 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163453, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163453, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163454 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163454, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163454, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163455 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163455, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163455, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163456 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163456, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163456, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163457 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163457, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163457, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35732 (p : Pattern) (ha : d142666 p = 1) (hb : d163463 p = 1) : d121355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d142666 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35182 q ha hb
    | true =>
      simp only [d14062, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35183 q ha hb
  have h2 (q : Pattern) (ha : d14063 q = 1) (hb : d142666 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163445 q = 1) : d121345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163445, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163445, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163446 q = 1) : d121346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163446, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163446, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163448 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163448, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163448, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35730 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163449 q = 1) : d121347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163449, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163449, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163450 q = 1) : d121348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163450, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163450, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163451 q = 1) : d121349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163451, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163451, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163452 q = 1) : d121350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163452, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163452, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163458 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163458, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163458, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35731 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163459 q = 1) : d121351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163459, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163459, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163460 q = 1) : d121352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163460, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163460, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163461 q = 1) : d121353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163461, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163461, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163462 q = 1) : d121354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163462, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163462, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163463 q = 1) : d121355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163463, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163463, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35733 (p : Pattern) (ha : d142666 p = 1) (hb : d163469 p = 1) : d121361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26904 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163464 q = 1) : d121356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163464, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163464, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35732 q ha hb
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163465 q = 1) : d121357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163465, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163465, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163466 q = 1) : d121358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163466, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163466, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163467 q = 1) : d121359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163467, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163467, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163468 q = 1) : d121360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163468, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163468, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163469 q = 1) : d121361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163469, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163469, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35734 (p : Pattern) (ha : d142666 p = 1) (hb : d163472 p = 1) : d168947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14235 q = 1) (hb : d142666 q = 1) : d167966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35210 q ha hb
    | true =>
      simp only [d14235, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35211 q ha hb
  have h2 (q : Pattern) (ha : d14236 q = 1) (hb : d142666 q = 1) : d168022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14237 q = 1) (hb : d142666 q = 1) : d168023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14237, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14238 q = 1) (hb : d142666 q = 1) : d168024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14239 q = 1) (hb : d142666 q = 1) : d168025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163472 q = 1) : d168947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163472, d168947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163472, d168947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35735 (p : Pattern) (ha : d142666 p = 1) (hb : d163483 p = 1) : d168957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163478 q = 1) : d167997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163478, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35240 q hb ha
    | true =>
      simp only [d163478, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35217 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163479 q = 1) : d168953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163479, d168953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163479, d168953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163480 q = 1) : d168954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163480, d168954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163480, d168954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163481 q = 1) : d168955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163481, d168955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163481, d168955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163482 q = 1) : d168956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163482, d168956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163482, d168956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163483 q = 1) : d168957 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163483, d168957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163483, d168957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35736 (p : Pattern) (ha : d142666 p = 1) (hb : d163489 p = 1) : d168963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d142666 q = 1) : d168027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35209 q ha hb
    | true =>
      simp only [d14241, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35212 q ha hb
  have h2 (q : Pattern) (ha : d14242 q = 1) (hb : d142666 q = 1) : d168028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163470 q = 1) : d168945 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163470, d168945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163470, d168945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163471 q = 1) : d168946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163471, d168946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163471, d168946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163473 q = 1) : d168948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163473, d168948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163473, d168948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35734 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163474 q = 1) : d168949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163474, d168949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163474, d168949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163475 q = 1) : d168950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163475, d168950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163475, d168950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163476 q = 1) : d168951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163476, d168951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163476, d168951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163477 q = 1) : d168952 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163477, d168952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163477, d168952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163484 q = 1) : d168958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163484, d168958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163484, d168958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35735 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163485 q = 1) : d168959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163485, d168959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163485, d168959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163486 q = 1) : d168960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163486, d168960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163486, d168960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163487 q = 1) : d168961 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163487, d168961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163487, d168961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163488 q = 1) : d168962 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163488, d168962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163488, d168962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163489 q = 1) : d168963 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163489, d168963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163489, d168963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35737 (p : Pattern) (ha : d142666 p = 1) (hb : d163495 p = 1) : d168969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163490 q = 1) : d168964 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163490, d168964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163490, d168964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35736 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163491 q = 1) : d168965 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163491, d168965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163491, d168965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163492 q = 1) : d168966 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163492, d168966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163492, d168966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163493 q = 1) : d168967 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163493, d168967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163493, d168967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163494 q = 1) : d168968 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163494, d168968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163494, d168968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163495 q = 1) : d168969 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163495, d168969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163495, d168969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35738 (p : Pattern) (ha : d142666 p = 1) (hb : d163499 p = 1) : d168973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14502 q = 1) (hb : d142666 q = 1) : d168156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35251 q ha hb
    | true =>
      simp only [d14502, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35252 q ha hb
  have h2 (q : Pattern) (ha : d14503 q = 1) (hb : d142666 q = 1) : d168157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14504 q = 1) (hb : d142666 q = 1) : d168158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14504, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14505 q = 1) (hb : d142666 q = 1) : d168159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14506 q = 1) (hb : d142666 q = 1) : d168160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163499 q = 1) : d168973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163499, d168973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163499, d168973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35739 (p : Pattern) (ha : d142666 p = 1) (hb : d163510 p = 1) : d168984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163505 q = 1) : d168979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163505, d168979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35282 q hb ha
    | true =>
      simp only [d163505, d168979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35259 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163506 q = 1) : d168980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163506, d168980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163506, d168980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163507 q = 1) : d168981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163507, d168981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163507, d168981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163508 q = 1) : d168982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163508, d168982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163508, d168982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163509 q = 1) : d168983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163509, d168983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163509, d168983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163510 q = 1) : d168984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163510, d168984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163510, d168984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35740 (p : Pattern) (ha : d142666 p = 1) (hb : d163516 p = 1) : d168990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d142666 q = 1) : d168162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35250 q ha hb
    | true =>
      simp only [d14508, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35253 q ha hb
  have h2 (q : Pattern) (ha : d14509 q = 1) (hb : d142666 q = 1) : d168163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163497 q = 1) : d168971 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163497, d168971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163497, d168971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163498 q = 1) : d168972 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163498, d168972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163498, d168972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163500 q = 1) : d168974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163500, d168974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163500, d168974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35738 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163501 q = 1) : d168975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163501, d168975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163501, d168975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163502 q = 1) : d168976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163502, d168976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163502, d168976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163503 q = 1) : d168977 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163503, d168977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163503, d168977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163504 q = 1) : d168978 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163504, d168978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163504, d168978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163511 q = 1) : d168985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163511, d168985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163511, d168985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35739 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163512 q = 1) : d168986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163512, d168986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163512, d168986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163513 q = 1) : d168987 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163513, d168987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163513, d168987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163514 q = 1) : d168988 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163514, d168988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163514, d168988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163515 q = 1) : d168989 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163515, d168989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163515, d168989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163516 q = 1) : d168990 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163516, d168990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163516, d168990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35741 (p : Pattern) (ha : d142666 p = 1) (hb : d163522 p = 1) : d168996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163517 q = 1) : d168991 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163517, d168991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163517, d168991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35740 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163518 q = 1) : d168992 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163518, d168992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163518, d168992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163519 q = 1) : d168993 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163519, d168993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163519, d168993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163520 q = 1) : d168994 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163520, d168994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163520, d168994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163521 q = 1) : d168995 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163521, d168995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163521, d168995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163522 q = 1) : d168996 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163522, d168996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163522, d168996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35742 (p : Pattern) (ha : d142666 p = 1) (hb : d163527 p = 1) : d169001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14809 q = 1) (hb : d142666 q = 1) : d168319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35294 q ha hb
    | true =>
      simp only [d14809, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35295 q ha hb
  have h2 (q : Pattern) (ha : d14810 q = 1) (hb : d142666 q = 1) : d168320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14811 q = 1) (hb : d142666 q = 1) : d168321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14811, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14812 q = 1) (hb : d142666 q = 1) : d168322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14813 q = 1) (hb : d142666 q = 1) : d168323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163527 q = 1) : d169001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163527, d169001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163527, d169001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35743 (p : Pattern) (ha : d142666 p = 1) (hb : d163534 p = 1) : d168438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15016 q = 1) (hb : d142666 q = 1) : d168423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35326 q ha hb
    | true =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15017 q = 1) (hb : d142666 q = 1) : d168424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15018 q = 1) (hb : d142666 q = 1) : d168425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15025 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15026 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15027 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15028 q = 1) (hb : d142666 q = 1) : d168431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15042 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15043 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15043, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15044 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15045 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15046 q = 1) (hb : d142666 q = 1) : d168436 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15046, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163533 q = 1) : d168437 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163533, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d163533, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d142666 q = 1) (hb : d163534 q = 1) : d168438 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163534, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163534, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35744 (p : Pattern) (ha : d142666 p = 1) (hb : d163540 p = 1) : d168452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163535 q = 1) : d168439 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163535, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35743 q ha hb
    | true =>
      simp only [d163535, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163536 q = 1) : d168440 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163536, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163536, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d142666 q = 1) : d168447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35303 q ha hb
    | true =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d142666 q = 1) : d168448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163537 q = 1) : d168449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163537, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163537, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163538 q = 1) : d168450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163538, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163538, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163539 q = 1) : d168451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163539, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163539, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163540 q = 1) : d168452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163540, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163540, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35745 (p : Pattern) (ha : d142666 p = 1) (hb : d163546 p = 1) : d169012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163541 q = 1) : d169007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163541, d169007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35744 q ha hb
    | true =>
      simp only [d163541, d169007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35304 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163542 q = 1) : d169008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163542, d169008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163542, d169008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163543 q = 1) : d169009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163543, d169009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163543, d169009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163544 q = 1) : d169010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163544, d169010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163544, d169010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163545 q = 1) : d169011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163545, d169011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163545, d169011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163546 q = 1) : d169012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163546, d169012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163546, d169012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35746 (p : Pattern) (ha : d142666 p = 1) (hb : d163552 p = 1) : d169018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d142666 q = 1) : d168325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35293 q ha hb
    | true =>
      simp only [d14815, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35296 q ha hb
  have h2 (q : Pattern) (ha : d14816 q = 1) (hb : d142666 q = 1) : d168326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163525 q = 1) : d168999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163525, d168999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163525, d168999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163526 q = 1) : d169000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163526, d169000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163526, d169000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163528 q = 1) : d169002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163528, d169002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163528, d169002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35742 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163529 q = 1) : d169003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163529, d169003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163529, d169003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163530 q = 1) : d169004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163530, d169004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163530, d169004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163531 q = 1) : d169005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163531, d169005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163531, d169005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163532 q = 1) : d169006 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163532, d169006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163532, d169006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163547 q = 1) : d169013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163547, d169013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163547, d169013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35745 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163548 q = 1) : d169014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163548, d169014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163548, d169014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163549 q = 1) : d169015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163549, d169015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163549, d169015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163550 q = 1) : d169016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163550, d169016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163550, d169016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163551 q = 1) : d169017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163551, d169017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163551, d169017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163552 q = 1) : d169018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163552, d169018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163552, d169018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35747 (p : Pattern) (ha : d142666 p = 1) (hb : d163558 p = 1) : d169024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163553 q = 1) : d169019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163553, d169019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163553, d169019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35746 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163554 q = 1) : d169020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163554, d169020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163554, d169020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163555 q = 1) : d169021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163555, d169021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163555, d169021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163556 q = 1) : d169022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163556, d169022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163556, d169022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163557 q = 1) : d169023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163557, d169023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163557, d169023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163558 q = 1) : d169024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163558, d169024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163558, d169024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35748 (p : Pattern) (ha : d142666 p = 1) (hb : d163564 p = 1) : d169030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15202 q = 1) (hb : d142666 q = 1) : d168527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35343 q ha hb
    | true =>
      simp only [d15202, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35344 q ha hb
  have h2 (q : Pattern) (ha : d15203 q = 1) (hb : d142666 q = 1) : d168528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15204 q = 1) (hb : d142666 q = 1) : d168529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15204, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15205 q = 1) (hb : d142666 q = 1) : d168530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15206 q = 1) (hb : d142666 q = 1) : d168531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163564 q = 1) : d169030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163564, d169030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163564, d169030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35749 (p : Pattern) (ha : d142666 p = 1) (hb : d163571 p = 1) : d168646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15409 q = 1) (hb : d142666 q = 1) : d168631 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35375 q ha hb
    | true =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15410 q = 1) (hb : d142666 q = 1) : d168632 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15411 q = 1) (hb : d142666 q = 1) : d168633 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15418 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15419 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15420 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15421 q = 1) (hb : d142666 q = 1) : d168639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15435 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15436 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15436, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15437 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15438 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15439 q = 1) (hb : d142666 q = 1) : d168644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15439, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163570 q = 1) : d168645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163570, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d163570, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d142666 q = 1) (hb : d163571 q = 1) : d168646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163571, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163571, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
end NetHack.Soko22Hazard87
