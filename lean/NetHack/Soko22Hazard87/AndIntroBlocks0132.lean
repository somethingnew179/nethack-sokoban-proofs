import NetHack.Soko22Hazard87.AndIntroBlocks0131
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro33000 (p : Pattern) (ha : d112688 p = 1) (hb : d150457 p = 1) : d115147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13586 q = 1) (hb : d112688 q = 1) : d13586 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150452 q = 1) : d115142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d115142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32999 q ha hb
    | true =>
      simp only [d150452, d115142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150453 q = 1) : d115143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150453, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150454 q = 1) : d115144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150454, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150455 q = 1) : d115145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150455, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150456 q = 1) : d115146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150456, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150457 q = 1) : d115147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150457, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33001 (p : Pattern) (ha : d112688 p = 1) (hb : d150463 p = 1) : d115153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d112688 q = 1) : d114715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32748 q ha hb
    | true =>
      simp only [d13324, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32750 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d112688 q = 1) : d114716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150440 q = 1) : d115134 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150440, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150441 q = 1) : d115135 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150441, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150443 q = 1) : d115137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150443, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32998 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150444 q = 1) : d115138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150445 q = 1) : d115139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150446 q = 1) : d115140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150447 q = 1) : d115141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150458 q = 1) : d115148 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150458, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33000 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150459 q = 1) : d115149 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150460 q = 1) : d115150 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150461 q = 1) : d115151 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150462 q = 1) : d115152 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150463 q = 1) : d115153 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33002 (p : Pattern) (ha : d112688 p = 1) (hb : d150469 p = 1) : d115159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150464 q = 1) : d115154 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150464, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33001 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150465 q = 1) : d115155 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150465, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150466 q = 1) : d115156 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150466, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150467 q = 1) : d115157 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150467, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150468 q = 1) : d115158 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150468, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150469 q = 1) : d115159 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150469, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33003 (p : Pattern) (ha : d112688 p = 1) (hb : d150476 p = 1) : d115166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13644 q = 1) (hb : d112688 q = 1) : d13644 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13645 q = 1) (hb : d112688 q = 1) : d114854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32779 q ha hb
    | true =>
      simp only [d13645, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13646 q = 1) (hb : d112688 q = 1) : d114855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13647 q = 1) (hb : d112688 q = 1) : d114856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13647, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13648 q = 1) (hb : d112688 q = 1) : d114857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13649 q = 1) (hb : d112688 q = 1) : d114858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150476 q = 1) : d115166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150476, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro33004 (p : Pattern) (ha : d112688 p = 1) (hb : d150485 p = 1) : d114952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d112688 q = 1) : d114943 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32801 q ha hb
    | true =>
      simp only [d13897, d114943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d112688 q = 1) : d114944 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d114944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13851 q = 1) (hb : d112688 q = 1) : d13851 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150482 q = 1) : d114949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150482, d114949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150483 q = 1) : d114950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150483, d114950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150484 q = 1) : d114951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150484, d114951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150485 q = 1) : d114952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150485, d114952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro33005 (p : Pattern) (ha : d112688 p = 1) (hb : d150491 p = 1) : d115177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13913 q = 1) (hb : d112688 q = 1) : d13913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150486 q = 1) : d115172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d115172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33004 q ha hb
    | true =>
      simp only [d150486, d115172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150487 q = 1) : d115173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150487, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150488 q = 1) : d115174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150488, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150489 q = 1) : d115175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150489, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150490 q = 1) : d115176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150490, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150491 q = 1) : d115177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150491, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33006 (p : Pattern) (ha : d112688 p = 1) (hb : d150497 p = 1) : d115183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d112688 q = 1) : d114860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32778 q ha hb
    | true =>
      simp only [d13651, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32780 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d112688 q = 1) : d114861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150474 q = 1) : d115164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150474, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150475 q = 1) : d115165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150475, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150477 q = 1) : d115167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150477, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33003 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150478 q = 1) : d115168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150479 q = 1) : d115169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150480 q = 1) : d115170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150481 q = 1) : d115171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150492 q = 1) : d115178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150492, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33005 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150493 q = 1) : d115179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150494 q = 1) : d115180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150495 q = 1) : d115181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150496 q = 1) : d115182 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150497 q = 1) : d115183 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33007 (p : Pattern) (ha : d112688 p = 1) (hb : d150503 p = 1) : d115189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150498 q = 1) : d115184 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150498, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33006 q ha hb
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150499 q = 1) : d115185 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150499, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150500 q = 1) : d115186 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150500, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150501 q = 1) : d115187 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150501, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150502 q = 1) : d115188 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150502, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150503 q = 1) : d115189 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150503, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33008 (p : Pattern) (ha : d112688 p = 1) (hb : d150509 p = 1) : d115195 p = 1 := by
  have h0 (q : Pattern) (ha : d112688 q = 1) (hb : d150378 q = 1) : d115076 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32984 q ha hb
    | true =>
      simp only [d150378, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32988 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150405 q = 1) : d115103 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150405, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32992 q ha hb
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150406 q = 1) : d115104 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150437 q = 1) : d115131 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150437, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32997 q ha hb
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150438 q = 1) : d115132 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150438, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150439 q = 1) : d115133 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112688 q = 1) (hb : d150470 q = 1) : d115160 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150470, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33002 q ha hb
  have h8 (q : Pattern) (ha : d112688 q = 1) (hb : d150471 q = 1) : d115161 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150471, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112688 q = 1) (hb : d150472 q = 1) : d115162 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150472, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112688 q = 1) (hb : d150473 q = 1) : d115163 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112688 q = 1) (hb : d150504 q = 1) : d115190 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150504, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33007 q ha hb
  have h12 (q : Pattern) (ha : d112688 q = 1) (hb : d150505 q = 1) : d115191 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150505, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112688 q = 1) (hb : d150506 q = 1) : d115192 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150506, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112688 q = 1) (hb : d150507 q = 1) : d115193 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150507, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112688 q = 1) (hb : d150508 q = 1) : d115194 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112688 q = 1) (hb : d150509 q = 1) : d115195 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro33009 (p : Pattern) (ha : d112688 p = 1) (hb : d150515 p = 1) : d115201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150510 q = 1) : d115196 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33008 q ha hb
    | true =>
      simp only [d150510, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150511 q = 1) : d115197 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150512 q = 1) : d115198 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150513 q = 1) : d115199 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150514 q = 1) : d115200 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150515 q = 1) : d115201 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33010 (p : Pattern) (ha : d112688 p = 1) (hb : d150521 p = 1) : d115207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150516 q = 1) : d115202 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33009 q ha hb
    | true =>
      simp only [d150516, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150517 q = 1) : d115203 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150518 q = 1) : d115204 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150519 q = 1) : d115205 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150520 q = 1) : d115206 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150521 q = 1) : d115207 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33011 (p : Pattern) (ha : d112688 p = 1) (hb : d150527 p = 1) : d115213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150522 q = 1) : d115208 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33010 q ha hb
    | true =>
      simp only [d150522, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150523 q = 1) : d115209 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150524 q = 1) : d115210 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150525 q = 1) : d115211 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150526 q = 1) : d115212 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150527 q = 1) : d115213 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33012 (p : Pattern) (ha : d112688 p = 1) (hb : d150533 p = 1) : d115219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150528 q = 1) : d115214 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33011 q ha hb
    | true =>
      simp only [d150528, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150529 q = 1) : d115215 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150530 q = 1) : d115216 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150531 q = 1) : d115217 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150532 q = 1) : d115218 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150533 q = 1) : d115219 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33013 (p : Pattern) (ha : d112688 p = 1) (hb : d150539 p = 1) : d115225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150534 q = 1) : d115220 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33012 q ha hb
    | true =>
      simp only [d150534, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150535 q = 1) : d115221 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150536 q = 1) : d115222 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150537 q = 1) : d115223 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150538 q = 1) : d115224 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150539 q = 1) : d115225 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33014 (p : Pattern) (ha : d112688 p = 1) (hb : d150545 p = 1) : d115231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150540 q = 1) : d115226 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33013 q ha hb
    | true =>
      simp only [d150540, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150541 q = 1) : d115227 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150542 q = 1) : d115228 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150543 q = 1) : d115229 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150544 q = 1) : d115230 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150545 q = 1) : d115231 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33015 (p : Pattern) (ha : d112688 p = 1) (hb : d150551 p = 1) : d115237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112688 q = 1) (hb : d150546 q = 1) : d115232 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33014 q ha hb
    | true =>
      simp only [d150546, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112688 q = 1) (hb : d150547 q = 1) : d115233 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112688 q = 1) (hb : d150548 q = 1) : d115234 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112688 q = 1) (hb : d150549 q = 1) : d115235 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112688 q = 1) (hb : d150550 q = 1) : d115236 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112688 q = 1) (hb : d150551 q = 1) : d115237 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33016 (p : Pattern) (ha : d83767 p = 1) (hb : d114162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d83757 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83757, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83764 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83764, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83765 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83765, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83766 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83766, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83767 q = 1) (hb : d114162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33017 (p : Pattern) (ha : d83786 p = 1) (hb : d114169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83671 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32815 q ha hb
    | true =>
      simp only [d83671, d114108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d83757 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83757, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83764 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83764, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83765 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83765, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83766 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83766, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83772 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83776 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83678 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
    | true =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d83779 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83779, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83783 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83783, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83784 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83784, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83785 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83785, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83786 q = 1) (hb : d114169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83786, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33018 (p : Pattern) (ha : d83795 p = 1) (hb : d115027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83678 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32817 q ha hb
    | true =>
      simp only [d83678, d114115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83779, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83783 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83793 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83794 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83795 q = 1) (hb : d115027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33019 (p : Pattern) (ha : d83820 p = 1) (hb : d115037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83704 q = 1) (hb : d114141 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32821 q ha hb
    | true =>
      simp only [d83704, d114141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d115033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83810, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83817 q = 1) (hb : d115034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83818 q = 1) (hb : d115035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83819 q = 1) (hb : d115036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83820 q = 1) (hb : d115037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33020 (p : Pattern) (ha : d83826 p = 1) (hb : d115043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83787 q = 1) (hb : d114170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33016 q ha hb
    | true =>
      simp only [d83787, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33017 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83790 q = 1) (hb : d114171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83790, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83791 q = 1) (hb : d115025 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83791, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83792 q = 1) (hb : d115026 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83792, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83796 q = 1) (hb : d115028 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83796, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33018 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83797 q = 1) (hb : d115029 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83797, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83798 q = 1) (hb : d115030 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83798, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83799 q = 1) (hb : d115031 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83799, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83800 q = 1) (hb : d115032 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83800, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83821 q = 1) (hb : d115038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83821, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33019 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83822 q = 1) (hb : d115039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83822, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83823 q = 1) (hb : d115040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83823, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83824 q = 1) (hb : d115041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83824, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83825 q = 1) (hb : d115042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83825, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83826 q = 1) (hb : d115043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83826, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33021 (p : Pattern) (ha : d83832 p = 1) (hb : d115049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d83716 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10167 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d83717 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d83718 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d83719 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d83720 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83827 q = 1) (hb : d115044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83827, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33020 q ha hb
  have h8 (q : Pattern) (ha : d83828 q = 1) (hb : d115045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83828, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83829 q = 1) (hb : d115046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83829, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83830 q = 1) (hb : d115047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83830, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83831 q = 1) (hb : d115048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83831, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83832 q = 1) (hb : d115049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d83832, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro33022 (p : Pattern) (ha : d83886 p = 1) (hb : d114281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83837 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
    | true =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h5 (q : Pattern) (ha : d83876 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83876, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83883 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83883, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83884 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83884, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83885 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83885, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83886 q = 1) (hb : d114281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33023 (p : Pattern) (ha : d83905 p = 1) (hb : d114290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83837 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32845 q ha hb
    | true =>
      simp only [d83837, d114276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h4 (q : Pattern) (ha : d83876 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83876, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83883 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83883, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83884 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83884, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83885 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83885, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83895 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83846 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32847 q ha hb
    | true =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h13 (q : Pattern) (ha : d83898 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83902 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83902, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83903 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83903, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83904 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83904, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83905 q = 1) (hb : d114290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83905, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33024 (p : Pattern) (ha : d83914 p = 1) (hb : d115052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83846 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32847 q ha hb
    | true =>
      simp only [d83846, d114285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83898, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83902 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83912 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83913 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83914 q = 1) (hb : d115052 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33025 (p : Pattern) (ha : d83944 p = 1) (hb : d115063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83933 q = 1) (hb : d115058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83933, d115058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32864 q ha hb
    | true =>
      simp only [d83933, d115058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28709 q hb ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d115059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83934, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83941 q = 1) (hb : d115060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83942 q = 1) (hb : d115061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83943 q = 1) (hb : d115062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83944 q = 1) (hb : d115063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33026 (p : Pattern) (ha : d83950 p = 1) (hb : d115069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83906 q = 1) (hb : d114291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33022 q ha hb
    | true =>
      simp only [d83906, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33023 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83909 q = 1) (hb : d114292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83909, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83910 q = 1) (hb : d115050 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83910, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83911 q = 1) (hb : d115051 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83911, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83915 q = 1) (hb : d115053 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83915, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33024 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83916 q = 1) (hb : d115054 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83916, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83917 q = 1) (hb : d115055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83917, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83918 q = 1) (hb : d115056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83918, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83919 q = 1) (hb : d115057 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83919, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83945 q = 1) (hb : d115064 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83945, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33025 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83946 q = 1) (hb : d115065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83946, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83947 q = 1) (hb : d115066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83947, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83948 q = 1) (hb : d115067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83948, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83949 q = 1) (hb : d115068 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83949, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83950 q = 1) (hb : d115069 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83950, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33027 (p : Pattern) (ha : d83956 p = 1) (hb : d115075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d115070 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33026 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d115071 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d115072 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d115073 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d115074 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d115075 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33028 (p : Pattern) (ha : d84015 p = 1) (hb : d114418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83966 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
    | true =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h5 (q : Pattern) (ha : d84005 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84005, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84012 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84012, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84013 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84013, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84014 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84014, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84015 q = 1) (hb : d114418 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33029 (p : Pattern) (ha : d84034 p = 1) (hb : d114427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83966 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32870 q ha hb
    | true =>
      simp only [d83966, d114413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q hb ha
  have h4 (q : Pattern) (ha : d84005 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84005, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84012 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84012, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84013 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84013, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84014 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84014, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84020 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83975 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32872 q ha hb
    | true =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q hb ha
  have h13 (q : Pattern) (ha : d84027 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84027, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84031 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84031, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84032 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84032, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84033 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84033, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84034 q = 1) (hb : d114427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84034, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33030 (p : Pattern) (ha : d84043 p = 1) (hb : d115079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83975 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32872 q ha hb
    | true =>
      simp only [d83975, d114422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q hb ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84027, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84031 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84041 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84042 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84043 q = 1) (hb : d115079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33031 (p : Pattern) (ha : d84077 p = 1) (hb : d115090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84066 q = 1) (hb : d115085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84066, d115085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32890 q ha hb
    | true =>
      simp only [d84066, d115085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28751 q hb ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d115086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84067, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84074 q = 1) (hb : d115087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84075 q = 1) (hb : d115088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84076 q = 1) (hb : d115089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84077 q = 1) (hb : d115090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33032 (p : Pattern) (ha : d84083 p = 1) (hb : d115096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84035 q = 1) (hb : d114428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33028 q ha hb
    | true =>
      simp only [d84035, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33029 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84038 q = 1) (hb : d114429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84038, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84039 q = 1) (hb : d115077 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84039, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84040 q = 1) (hb : d115078 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84040, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84044 q = 1) (hb : d115080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84044, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33030 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84045 q = 1) (hb : d115081 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84045, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84046 q = 1) (hb : d115082 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84046, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84047 q = 1) (hb : d115083 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84047, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84048 q = 1) (hb : d115084 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84048, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84078 q = 1) (hb : d115091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84078, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33031 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84079 q = 1) (hb : d115092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84079, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84080 q = 1) (hb : d115093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84080, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84081 q = 1) (hb : d115094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84081, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84082 q = 1) (hb : d115095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84082, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84083 q = 1) (hb : d115096 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84083, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33033 (p : Pattern) (ha : d84089 p = 1) (hb : d115102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d115097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33032 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d115098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d115099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d115100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d115101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d115102 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33034 (p : Pattern) (ha : d84149 p = 1) (hb : d114561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84100 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
    | true =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q hb ha
  have h5 (q : Pattern) (ha : d84139 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84139, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84146 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84146, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84147 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84147, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84148 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84148, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84149 q = 1) (hb : d114561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33035 (p : Pattern) (ha : d84168 p = 1) (hb : d114570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84100 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32896 q ha hb
    | true =>
      simp only [d84100, d114556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28791 q hb ha
  have h4 (q : Pattern) (ha : d84139 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84139, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84146 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84146, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84147 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84147, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84148 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84148, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84154 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84109 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32898 q ha hb
    | true =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28792 q hb ha
  have h13 (q : Pattern) (ha : d84161 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84161, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84165 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84165, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84166 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84166, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84167 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84167, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84168 q = 1) (hb : d114570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84168, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33036 (p : Pattern) (ha : d84177 p = 1) (hb : d115107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84109 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32898 q ha hb
    | true =>
      simp only [d84109, d114565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28792 q hb ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84161, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84165 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84175 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84176 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84177 q = 1) (hb : d115107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33037 (p : Pattern) (ha : d84211 p = 1) (hb : d115118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84200 q = 1) (hb : d115113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84200, d115113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32916 q ha hb
    | true =>
      simp only [d84200, d115113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28797 q hb ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d115114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84201, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84208 q = 1) (hb : d115115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84209 q = 1) (hb : d115116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84210 q = 1) (hb : d115117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84211 q = 1) (hb : d115118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33038 (p : Pattern) (ha : d84217 p = 1) (hb : d115124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84169 q = 1) (hb : d114571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33034 q ha hb
    | true =>
      simp only [d84169, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33035 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84172 q = 1) (hb : d114572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84172, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84173 q = 1) (hb : d115105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84173, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84174 q = 1) (hb : d115106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84174, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84178 q = 1) (hb : d115108 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84178, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33036 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84179 q = 1) (hb : d115109 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84179, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84180 q = 1) (hb : d115110 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84180, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84181 q = 1) (hb : d115111 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84181, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84182 q = 1) (hb : d115112 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84182, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84212 q = 1) (hb : d115119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84212, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33037 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84213 q = 1) (hb : d115120 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84213, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84214 q = 1) (hb : d115121 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84214, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84215 q = 1) (hb : d115122 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84215, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84216 q = 1) (hb : d115123 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84216, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84217 q = 1) (hb : d115124 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84217, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33039 (p : Pattern) (ha : d84223 p = 1) (hb : d115130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d115125 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33038 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d115126 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d115127 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d115128 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d115129 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d115130 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33040 (p : Pattern) (ha : d84284 p = 1) (hb : d114705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84235 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
    | true =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q hb ha
  have h5 (q : Pattern) (ha : d84274 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84274, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84281 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84281, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84282 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84282, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84283 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84283, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84284 q = 1) (hb : d114705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33041 (p : Pattern) (ha : d84303 p = 1) (hb : d114714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84235 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32922 q ha hb
    | true =>
      simp only [d84235, d114700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28837 q hb ha
  have h4 (q : Pattern) (ha : d84274 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84274, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84281 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84281, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84282 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84282, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84283 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84283, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84293 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84244 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32924 q ha hb
    | true =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28838 q hb ha
  have h13 (q : Pattern) (ha : d84296 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84296, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84300 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84300, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84301 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84301, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84302 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84302, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84303 q = 1) (hb : d114714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84303, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33042 (p : Pattern) (ha : d84312 p = 1) (hb : d115136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84244 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32924 q ha hb
    | true =>
      simp only [d84244, d114709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28838 q hb ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84296, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84300 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84310 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84311 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84312 q = 1) (hb : d115136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33043 (p : Pattern) (ha : d84346 p = 1) (hb : d115147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84335 q = 1) (hb : d115142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84335, d115142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32942 q ha hb
    | true =>
      simp only [d84335, d115142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28843 q hb ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d115143 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84336, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84343 q = 1) (hb : d115144 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84344 q = 1) (hb : d115145 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84345 q = 1) (hb : d115146 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84346 q = 1) (hb : d115147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33044 (p : Pattern) (ha : d84352 p = 1) (hb : d115153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84304 q = 1) (hb : d114715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33040 q ha hb
    | true =>
      simp only [d84304, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33041 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84307 q = 1) (hb : d114716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84307, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84308 q = 1) (hb : d115134 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84308, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84309 q = 1) (hb : d115135 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84309, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84313 q = 1) (hb : d115137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84313, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33042 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84314 q = 1) (hb : d115138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84314, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84315 q = 1) (hb : d115139 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84315, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84316 q = 1) (hb : d115140 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84316, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84317 q = 1) (hb : d115141 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84317, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84347 q = 1) (hb : d115148 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84347, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33043 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84348 q = 1) (hb : d115149 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84348, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84349 q = 1) (hb : d115150 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84349, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84350 q = 1) (hb : d115151 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84350, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84351 q = 1) (hb : d115152 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84351, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84352 q = 1) (hb : d115153 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84352, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33045 (p : Pattern) (ha : d84358 p = 1) (hb : d115159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d115154 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33044 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d115155 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d115156 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d115157 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d115158 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d115159 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33046 (p : Pattern) (ha : d84420 p = 1) (hb : d114850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84371 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
    | true =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h5 (q : Pattern) (ha : d84410 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84410, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84417 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84417, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84418 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84418, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84419 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84419, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84420 q = 1) (hb : d114850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33047 (p : Pattern) (ha : d84439 p = 1) (hb : d114859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84371 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32948 q ha hb
    | true =>
      simp only [d84371, d114845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28883 q hb ha
  have h4 (q : Pattern) (ha : d84410 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84410, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84417 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84417, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84418 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84418, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84419 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84419, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84425 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84380 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32950 q ha hb
    | true =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28884 q hb ha
  have h13 (q : Pattern) (ha : d84432 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84432, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84436 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84436, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84437 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84437, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84438 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84438, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84439 q = 1) (hb : d114859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84439, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33048 (p : Pattern) (ha : d84448 p = 1) (hb : d115166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84380 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32950 q ha hb
    | true =>
      simp only [d84380, d114854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28884 q hb ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84432, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84436 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84446 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84447 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84448 q = 1) (hb : d115166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33049 (p : Pattern) (ha : d84482 p = 1) (hb : d115177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84471 q = 1) (hb : d115172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84471, d115172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32968 q ha hb
    | true =>
      simp only [d84471, d115172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28889 q hb ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d115173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84472, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84479 q = 1) (hb : d115174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84480 q = 1) (hb : d115175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84481 q = 1) (hb : d115176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84482 q = 1) (hb : d115177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33050 (p : Pattern) (ha : d84488 p = 1) (hb : d115183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84440 q = 1) (hb : d114860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33046 q ha hb
    | true =>
      simp only [d84440, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33047 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84443 q = 1) (hb : d114861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84443, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84444 q = 1) (hb : d115164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84444, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84445 q = 1) (hb : d115165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84445, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84449 q = 1) (hb : d115167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84449, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33048 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84450 q = 1) (hb : d115168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84450, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84451 q = 1) (hb : d115169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84451, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84452 q = 1) (hb : d115170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84452, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84453 q = 1) (hb : d115171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84453, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84483 q = 1) (hb : d115178 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84483, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33049 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84484 q = 1) (hb : d115179 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84484, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84485 q = 1) (hb : d115180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84485, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84486 q = 1) (hb : d115181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84486, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84487 q = 1) (hb : d115182 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84487, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84488 q = 1) (hb : d115183 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84488, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33051 (p : Pattern) (ha : d84494 p = 1) (hb : d115189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d115184 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33050 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d115185 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d115186 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d115187 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d115188 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d115189 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33052 (p : Pattern) (ha : d84500 p = 1) (hb : d115195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d115076 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33021 q ha hb
    | true =>
      simp only [d83957, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33027 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d115103 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33033 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d115104 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d115131 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33039 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d115132 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d115133 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d115160 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33045 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d115161 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d115162 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d115163 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d115190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33051 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d115191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d115192 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d115193 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d115194 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d115195 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro33053 (p : Pattern) (ha : d84506 p = 1) (hb : d115201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d115196 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33052 q ha hb
    | true =>
      simp only [d84501, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d115197 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d115198 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d115199 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d115200 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d115201 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33054 (p : Pattern) (ha : d84512 p = 1) (hb : d115207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d115202 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33053 q ha hb
    | true =>
      simp only [d84507, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d115203 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d115204 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d115205 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d115206 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d115207 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33055 (p : Pattern) (ha : d84518 p = 1) (hb : d115213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d115208 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33054 q ha hb
    | true =>
      simp only [d84513, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d115209 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d115210 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d115211 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d115212 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d115213 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33056 (p : Pattern) (ha : d84524 p = 1) (hb : d115219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d115214 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33055 q ha hb
    | true =>
      simp only [d84519, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d115215 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d115216 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d115217 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d115218 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d115219 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33057 (p : Pattern) (ha : d84530 p = 1) (hb : d115225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d115220 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33056 q ha hb
    | true =>
      simp only [d84525, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d115221 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d115222 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d115223 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d115224 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d115225 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33058 (p : Pattern) (ha : d84536 p = 1) (hb : d115231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d115226 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33057 q ha hb
    | true =>
      simp only [d84531, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d115227 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d115228 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d115229 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d115230 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d115231 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33059 (p : Pattern) (ha : d84542 p = 1) (hb : d115237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d115232 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33058 q ha hb
    | true =>
      simp only [d84537, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d115233 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d115234 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d115235 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d115236 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d115237 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro33060 (p : Pattern) (ha : d85432 p = 1) (hb : d114162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85428 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85428, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85429 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85429, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85430 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85430, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85431 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85431, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85432 q = 1) (hb : d114162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d114162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33061 (p : Pattern) (ha : d85437 p = 1) (hb : d114169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114108 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85428 q = 1) (hb : d114158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85428, d114158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85429 q = 1) (hb : d114159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85429, d114159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85430 q = 1) (hb : d114160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85430, d114160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85431 q = 1) (hb : d114161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85431, d114161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7358 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7362 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85433 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85433, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85434 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85434, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85435 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85435, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85436 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85436, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85437 q = 1) (hb : d114169 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85437, d114169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33062 (p : Pattern) (ha : d85444 p = 1) (hb : d115027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85433 q = 1) (hb : d114165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85433, d114165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d114166 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85434, d114166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d114167 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d114167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d114168 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d114168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d115027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d115027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33063 (p : Pattern) (ha : d85454 p = 1) (hb : d115037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85450 q = 1) (hb : d115033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85450, d115033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d115034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85451, d115034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d115035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d115035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d115036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d115036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d115037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d115037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33064 (p : Pattern) (ha : d85460 p = 1) (hb : d115043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85438 q = 1) (hb : d114170 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33060 q ha hb
    | true =>
      simp only [d85438, d114170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33061 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85439 q = 1) (hb : d114171 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85439, d114171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85440 q = 1) (hb : d115025 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85440, d115025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85441 q = 1) (hb : d115026 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85441, d115026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85445 q = 1) (hb : d115028 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85445, d115028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33062 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85446 q = 1) (hb : d115029 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85446, d115029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85447 q = 1) (hb : d115030 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85447, d115030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85448 q = 1) (hb : d115031 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85448, d115031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85449 q = 1) (hb : d115032 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85449, d115032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85455 q = 1) (hb : d115038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85455, d115038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33063 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85456 q = 1) (hb : d115039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85456, d115039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85457 q = 1) (hb : d115040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85457, d115040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85458 q = 1) (hb : d115041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85458, d115041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85459 q = 1) (hb : d115042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85459, d115042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85460 q = 1) (hb : d115043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85460, d115043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33065 (p : Pattern) (ha : d85466 p = 1) (hb : d115049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d85423 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10216 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d85424 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d85425 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d85426 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d85427 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d115044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d115044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33064 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d115045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d115045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d115046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d115046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d115047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d115047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d115048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d115048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d115049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d85466, d115049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro33066 (p : Pattern) (ha : d85471 p = 1) (hb : d114281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85467 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85467, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85468 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85468, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85469 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85469, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85470 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85470, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85471 q = 1) (hb : d114281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d114281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33067 (p : Pattern) (ha : d85476 p = 1) (hb : d114290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85467 q = 1) (hb : d114277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85467, d114277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85468 q = 1) (hb : d114278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85468, d114278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85469 q = 1) (hb : d114279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85469, d114279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85470 q = 1) (hb : d114280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85470, d114280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85472 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85472, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85473 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85473, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85474 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85474, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85475 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85475, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85476 q = 1) (hb : d114290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85476, d114290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33068 (p : Pattern) (ha : d85483 p = 1) (hb : d115052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85472 q = 1) (hb : d114286 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85472, d114286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d114287 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85473, d114287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d114288 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d114288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d114289 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d114289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d115052 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d115052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33069 (p : Pattern) (ha : d85493 p = 1) (hb : d115063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115058 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85489 q = 1) (hb : d115059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85489, d115059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d115060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85490, d115060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d115061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d115061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d115062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d115062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d115063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d115063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33070 (p : Pattern) (ha : d85499 p = 1) (hb : d115069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85477 q = 1) (hb : d114291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33066 q ha hb
    | true =>
      simp only [d85477, d114291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33067 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7516 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85478 q = 1) (hb : d114292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85478, d114292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85479 q = 1) (hb : d115050 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85479, d115050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85480 q = 1) (hb : d115051 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85480, d115051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85484 q = 1) (hb : d115053 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85484, d115053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33068 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85485 q = 1) (hb : d115054 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85485, d115054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85486 q = 1) (hb : d115055 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85486, d115055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85487 q = 1) (hb : d115056 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85487, d115056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85488 q = 1) (hb : d115057 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85488, d115057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85494 q = 1) (hb : d115064 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85494, d115064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33069 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85495 q = 1) (hb : d115065 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85495, d115065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85496 q = 1) (hb : d115066 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85496, d115066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85497 q = 1) (hb : d115067 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85497, d115067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85498 q = 1) (hb : d115068 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85498, d115068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85499 q = 1) (hb : d115069 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85499, d115069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33071 (p : Pattern) (ha : d85505 p = 1) (hb : d115075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d115070 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d115070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33070 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d115071 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d115071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d115072 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d115072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d115073 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d115073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d115074 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d115074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d115075 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d115075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33072 (p : Pattern) (ha : d85511 p = 1) (hb : d114418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85507 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85507, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85508 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85508, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85509 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85509, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85510 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85510, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85511 q = 1) (hb : d114418 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d114418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33073 (p : Pattern) (ha : d85516 p = 1) (hb : d114427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114413 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85507 q = 1) (hb : d114414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85507, d114414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85508 q = 1) (hb : d114415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85508, d114415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85509 q = 1) (hb : d114416 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85509, d114416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85510 q = 1) (hb : d114417 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85510, d114417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7649 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85512 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85512, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85513 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85513, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85514 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85514, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85515 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85515, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85516 q = 1) (hb : d114427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85516, d114427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33074 (p : Pattern) (ha : d85523 p = 1) (hb : d115079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85512 q = 1) (hb : d114423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85512, d114423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d114424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85513, d114424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d114425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d114425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d114426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d114426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d115079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d115079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33075 (p : Pattern) (ha : d85533 p = 1) (hb : d115090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115085 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85529 q = 1) (hb : d115086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85529, d115086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d115087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85530, d115087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d115088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d115088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d115089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d115089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d115090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d115090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33076 (p : Pattern) (ha : d85539 p = 1) (hb : d115096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85517 q = 1) (hb : d114428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33072 q ha hb
    | true =>
      simp only [d85517, d114428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33073 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85518 q = 1) (hb : d114429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85518, d114429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85519 q = 1) (hb : d115077 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85519, d115077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85520 q = 1) (hb : d115078 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85520, d115078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85524 q = 1) (hb : d115080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85524, d115080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33074 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85525 q = 1) (hb : d115081 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85525, d115081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85526 q = 1) (hb : d115082 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85526, d115082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85527 q = 1) (hb : d115083 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85527, d115083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85528 q = 1) (hb : d115084 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85528, d115084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85534 q = 1) (hb : d115091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85534, d115091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33075 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85535 q = 1) (hb : d115092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85535, d115092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85536 q = 1) (hb : d115093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85536, d115093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85537 q = 1) (hb : d115094 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85537, d115094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85538 q = 1) (hb : d115095 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85538, d115095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85539 q = 1) (hb : d115096 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85539, d115096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33077 (p : Pattern) (ha : d85545 p = 1) (hb : d115102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d115097 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d115097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33076 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d115098 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d115098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d115099 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d115099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d115100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d115100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d115101 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d115101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d115102 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d115102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33078 (p : Pattern) (ha : d85552 p = 1) (hb : d114561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85548 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85548, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85549 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85549, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85550 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85550, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85551 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85551, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85552 q = 1) (hb : d114561 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d114561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33079 (p : Pattern) (ha : d85557 p = 1) (hb : d114570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114556 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85548 q = 1) (hb : d114557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85548, d114557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85549 q = 1) (hb : d114558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85549, d114558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85550 q = 1) (hb : d114559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85550, d114559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85551 q = 1) (hb : d114560 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85551, d114560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7798 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7802 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85553 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85553, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85554 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85554, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85555 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85555, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85556 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85556, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85557 q = 1) (hb : d114570 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85557, d114570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33080 (p : Pattern) (ha : d85564 p = 1) (hb : d115107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85553 q = 1) (hb : d114566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85553, d114566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d114567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85554, d114567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d114568 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d114568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d114569 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d114569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d115107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d115107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33081 (p : Pattern) (ha : d85574 p = 1) (hb : d115118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115113 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85570 q = 1) (hb : d115114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85570, d115114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d115115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85571, d115115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d115116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d115116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d115117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d115117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d115118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d115118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33082 (p : Pattern) (ha : d85580 p = 1) (hb : d115124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85558 q = 1) (hb : d114571 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33078 q ha hb
    | true =>
      simp only [d85558, d114571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33079 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85559 q = 1) (hb : d114572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85559, d114572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85560 q = 1) (hb : d115105 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85560, d115105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85561 q = 1) (hb : d115106 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85561, d115106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85565 q = 1) (hb : d115108 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85565, d115108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33080 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85566 q = 1) (hb : d115109 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85566, d115109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85567 q = 1) (hb : d115110 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85567, d115110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85568 q = 1) (hb : d115111 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85568, d115111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85569 q = 1) (hb : d115112 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85569, d115112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85575 q = 1) (hb : d115119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85575, d115119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33081 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85576 q = 1) (hb : d115120 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85576, d115120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85577 q = 1) (hb : d115121 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85577, d115121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85578 q = 1) (hb : d115122 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85578, d115122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85579 q = 1) (hb : d115123 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85579, d115123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85580 q = 1) (hb : d115124 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85580, d115124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33083 (p : Pattern) (ha : d85586 p = 1) (hb : d115130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d115125 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d115125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33082 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d115126 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d115126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d115127 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d115127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d115128 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d115128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d115129 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d115129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d115130 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d115130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33084 (p : Pattern) (ha : d85594 p = 1) (hb : d114705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85590 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85590, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85591 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85591, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85592 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85592, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85593 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85593, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85594 q = 1) (hb : d114705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d114705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33085 (p : Pattern) (ha : d85599 p = 1) (hb : d114714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114700 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85590 q = 1) (hb : d114701 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85590, d114701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85591 q = 1) (hb : d114702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85591, d114702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85592 q = 1) (hb : d114703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85592, d114703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85593 q = 1) (hb : d114704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85593, d114704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85595 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85595, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85596 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85596, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85597 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85597, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85598 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85598, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85599 q = 1) (hb : d114714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85599, d114714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33086 (p : Pattern) (ha : d85606 p = 1) (hb : d115136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85595 q = 1) (hb : d114710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85595, d114710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d114711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85596, d114711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d114712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d114712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d114713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d114713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d115136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d115136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33087 (p : Pattern) (ha : d85616 p = 1) (hb : d115147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85612 q = 1) (hb : d115143 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85612, d115143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d115144 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85613, d115144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d115145 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d115145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d115146 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d115146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d115147 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d115147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33088 (p : Pattern) (ha : d85622 p = 1) (hb : d115153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85600 q = 1) (hb : d114715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33084 q ha hb
    | true =>
      simp only [d85600, d114715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7971 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85601 q = 1) (hb : d114716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85601, d114716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85602 q = 1) (hb : d115134 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85602, d115134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85603 q = 1) (hb : d115135 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85603, d115135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85607 q = 1) (hb : d115137 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85607, d115137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33086 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85608 q = 1) (hb : d115138 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85608, d115138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85609 q = 1) (hb : d115139 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85609, d115139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85610 q = 1) (hb : d115140 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85610, d115140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85611 q = 1) (hb : d115141 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85611, d115141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85617 q = 1) (hb : d115148 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85617, d115148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33087 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85618 q = 1) (hb : d115149 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85618, d115149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85619 q = 1) (hb : d115150 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85619, d115150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85620 q = 1) (hb : d115151 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85620, d115151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85621 q = 1) (hb : d115152 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85621, d115152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85622 q = 1) (hb : d115153 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85622, d115153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33089 (p : Pattern) (ha : d85628 p = 1) (hb : d115159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d115154 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d115154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33088 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d115155 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d115155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d115156 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d115156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d115157 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d115157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d115158 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d115158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d115159 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d115159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33090 (p : Pattern) (ha : d85637 p = 1) (hb : d114850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85633 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85633, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85634 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85634, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85635 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85635, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85636 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85636, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85637 q = 1) (hb : d114850 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d114850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33091 (p : Pattern) (ha : d85642 p = 1) (hb : d114859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d114845 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85633 q = 1) (hb : d114846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85633, d114846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85634 q = 1) (hb : d114847 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85634, d114847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85635 q = 1) (hb : d114848 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85635, d114848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85636 q = 1) (hb : d114849 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85636, d114849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8107 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8111 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85638 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85638, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85639 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85639, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85640 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85640, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85641 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85641, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85642 q = 1) (hb : d114859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85642, d114859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro33092 (p : Pattern) (ha : d85649 p = 1) (hb : d115166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85638 q = 1) (hb : d114855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85638, d114855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d114856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85639, d114856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d114857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d114857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d114858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d114858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d115166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d115166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33093 (p : Pattern) (ha : d85659 p = 1) (hb : d115177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d115172 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85655 q = 1) (hb : d115173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85655, d115173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d115174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85656, d115174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d115175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d115175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d115176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d115176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d115177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d115177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33094 (p : Pattern) (ha : d85665 p = 1) (hb : d115183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8061 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85643 q = 1) (hb : d114860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33090 q ha hb
    | true =>
      simp only [d85643, d114860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33091 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85644 q = 1) (hb : d114861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85644, d114861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85645 q = 1) (hb : d115164 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85645, d115164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85646 q = 1) (hb : d115165 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85646, d115165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85650 q = 1) (hb : d115167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85650, d115167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33092 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85651 q = 1) (hb : d115168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85651, d115168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85652 q = 1) (hb : d115169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85652, d115169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85653 q = 1) (hb : d115170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85653, d115170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85654 q = 1) (hb : d115171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85654, d115171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85660 q = 1) (hb : d115178 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85660, d115178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33093 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85661 q = 1) (hb : d115179 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85661, d115179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85662 q = 1) (hb : d115180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85662, d115180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85663 q = 1) (hb : d115181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85663, d115181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85664 q = 1) (hb : d115182 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85664, d115182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85665 q = 1) (hb : d115183 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85665, d115183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33095 (p : Pattern) (ha : d85671 p = 1) (hb : d115189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d115184 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d115184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33094 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d115185 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d115185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d115186 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d115186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d115187 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d115187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d115188 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d115188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d115189 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d115189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33096 (p : Pattern) (ha : d85677 p = 1) (hb : d115195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d115076 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33065 q ha hb
    | true =>
      simp only [d85506, d115076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33071 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d115103 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d115103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33077 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d115104 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d115104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d115131 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d115131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33083 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d115132 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d115132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d115133 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d115133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d115160 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d115160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33089 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d115161 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d115161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d115162 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d115162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d115163 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d115163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d115190 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d115190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33095 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d115191 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d115191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d115192 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d115192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d115193 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d115193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d115194 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d115194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d115195 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d115195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro33097 (p : Pattern) (ha : d85683 p = 1) (hb : d115201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d115196 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33096 q ha hb
    | true =>
      simp only [d85678, d115196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d115197 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d115197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d115198 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d115198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d115199 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d115199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d115200 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d115200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d115201 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d115201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33098 (p : Pattern) (ha : d85689 p = 1) (hb : d115207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d115202 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33097 q ha hb
    | true =>
      simp only [d85684, d115202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d115203 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d115203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d115204 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d115204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d115205 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d115205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d115206 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d115206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d115207 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d115207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33099 (p : Pattern) (ha : d85695 p = 1) (hb : d115213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d115208 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33098 q ha hb
    | true =>
      simp only [d85690, d115208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d115209 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d115209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d115210 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d115210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d115211 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d115211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d115212 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d115212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d115213 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d115213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33100 (p : Pattern) (ha : d85701 p = 1) (hb : d115219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d115214 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33099 q ha hb
    | true =>
      simp only [d85696, d115214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d115215 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d115215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d115216 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d115216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d115217 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d115217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d115218 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d115218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d115219 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d115219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33101 (p : Pattern) (ha : d85707 p = 1) (hb : d115225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d115220 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33100 q ha hb
    | true =>
      simp only [d85702, d115220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d115221 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d115221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d115222 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d115222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d115223 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d115223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d115224 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d115224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d115225 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d115225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33102 (p : Pattern) (ha : d85713 p = 1) (hb : d115231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d115226 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33101 q ha hb
    | true =>
      simp only [d85708, d115226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d115227 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d115227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d115228 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d115228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d115229 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d115229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d115230 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d115230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d115231 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d115231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33103 (p : Pattern) (ha : d85719 p = 1) (hb : d115237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d115232 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33102 q ha hb
    | true =>
      simp only [d85714, d115232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d115233 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d115233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d115234 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d115234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d115235 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d115235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d115236 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d115236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d115237 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d115237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33104 (p : Pattern) (ha : d12312 p = 1) (hb : d162092 p = 1) : d4913 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d323 q = 1) (hb : d162091 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d162091, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d162091, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12312 q = 1) (hb : d162092 q = 1) : d4913 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12312, d162092, d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33105 (p : Pattern) (ha : d12318 p = 1) (hb : d162092 p = 1) : d162101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4818 q = 1) (hb : d162092 q = 1) : d4818 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12313 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33104 q ha hb
    | true =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12314 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12315 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4821 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12316 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12225 q = 1) (hb : d162092 q = 1) : d12225 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12317 q = 1) (hb : d162092 q = 1) : d162100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12317, d162100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12318 q = 1) (hb : d162092 q = 1) : d162101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12318, d162101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33106 (p : Pattern) (ha : d12324 p = 1) (hb : d162092 p = 1) : d162107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d162092 q = 1) : d162102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33105 q ha hb
    | true =>
      simp only [d12319, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d162092 q = 1) : d162103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12229 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12321 q = 1) (hb : d162092 q = 1) : d162104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12322 q = 1) (hb : d162092 q = 1) : d162105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12322, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12323 q = 1) (hb : d162092 q = 1) : d162106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12323, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12324 q = 1) (hb : d162092 q = 1) : d162107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d162107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33107 (p : Pattern) (ha : d115280 p = 1) (hb : d162092 p = 1) : d162113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12305 q = 1) (hb : d162092 q = 1) : d12305 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12311 q = 1) (hb : d162092 q = 1) : d12311 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12233 q = 1) (hb : d162092 q = 1) : d12233 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12325 q = 1) (hb : d162092 q = 1) : d162108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33106 q ha hb
    | true =>
      simp only [d12325, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115276 q = 1) (hb : d162092 q = 1) : d162109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115276, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12346 q = 1) (hb : d162092 q = 1) : d12346 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115277 q = 1) (hb : d162092 q = 1) : d162110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115277, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115278 q = 1) (hb : d162092 q = 1) : d162111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115278, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115279 q = 1) (hb : d162092 q = 1) : d162112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115279, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115280 q = 1) (hb : d162092 q = 1) : d162113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d162113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33108 (p : Pattern) (ha : d12360 p = 1) (hb : d162092 p = 1) : d162114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d162092 q = 1) : d162102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33105 q ha hb
    | true =>
      simp only [d12319, d162102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d162092 q = 1) : d162103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d162103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12229 q = 1) (hb : d162092 q = 1) : d12229 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12321 q = 1) (hb : d162092 q = 1) : d162104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d162104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12322 q = 1) (hb : d162092 q = 1) : d162105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12322, d162105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12323 q = 1) (hb : d162092 q = 1) : d162106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12323, d162106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12360 q = 1) (hb : d162092 q = 1) : d162114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12360, d162114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33109 (p : Pattern) (ha : d115285 p = 1) (hb : d162092 p = 1) : d162120 p = 1 := by
  have h0 (q : Pattern) (ha : d12305 q = 1) (hb : d162092 q = 1) : d12305 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12311 q = 1) (hb : d162092 q = 1) : d12311 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12233 q = 1) (hb : d162092 q = 1) : d12233 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12325 q = 1) (hb : d162092 q = 1) : d162108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33106 q ha hb
    | true =>
      simp only [d12325, d162108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115276 q = 1) (hb : d162092 q = 1) : d162109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115276, d162109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12346 q = 1) (hb : d162092 q = 1) : d12346 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115277 q = 1) (hb : d162092 q = 1) : d162110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115277, d162110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115278 q = 1) (hb : d162092 q = 1) : d162111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115278, d162111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115279 q = 1) (hb : d162092 q = 1) : d162112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115279, d162112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12355 q = 1) (hb : d162092 q = 1) : d12355 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12359 q = 1) (hb : d162092 q = 1) : d12359 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12240 q = 1) (hb : d162092 q = 1) : d12240 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12361 q = 1) (hb : d162092 q = 1) : d162115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33108 q ha hb
    | true =>
      simp only [d12361, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115281 q = 1) (hb : d162092 q = 1) : d162116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115281, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d12367 q = 1) (hb : d162092 q = 1) : d12367 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d115282 q = 1) (hb : d162092 q = 1) : d162117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115282, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115283 q = 1) (hb : d162092 q = 1) : d162118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115283, d162118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115284 q = 1) (hb : d162092 q = 1) : d162119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115284, d162119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d115285 q = 1) (hb : d162092 q = 1) : d162120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115285, d162120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33110 (p : Pattern) (ha : d115292 p = 1) (hb : d162092 p = 1) : d162127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12240 q = 1) (hb : d162092 q = 1) : d12240 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12361 q = 1) (hb : d162092 q = 1) : d162115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33108 q ha hb
    | true =>
      simp only [d12361, d162115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115281 q = 1) (hb : d162092 q = 1) : d162116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115281, d162116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d162092 q = 1) : d12367 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d162092 q = 1) : d162117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115282, d162117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d162092 q = 1) : d162125 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d162125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d162092 q = 1) : d162126 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d162126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d162092 q = 1) : d162127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d162127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33111 (p : Pattern) (ha : d12386 p = 1) (hb : d162092 p = 1) : d6210 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d416 q = 1) (hb : d162091 q = 1) : d975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d162091, d975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d162091, d975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12386 q = 1) (hb : d162092 q = 1) : d6210 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12386, d162092, d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33112 (p : Pattern) (ha : d12392 p = 1) (hb : d162092 p = 1) : d162138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6078 q = 1) (hb : d162092 q = 1) : d6078 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12387 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33111 q ha hb
    | true =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12388 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12389 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6081 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12390 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12259 q = 1) (hb : d162092 q = 1) : d12259 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12391 q = 1) (hb : d162092 q = 1) : d162137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12391, d162137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12392 q = 1) (hb : d162092 q = 1) : d162138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12392, d162138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33113 (p : Pattern) (ha : d12398 p = 1) (hb : d162092 p = 1) : d162144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d162092 q = 1) : d162139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33112 q ha hb
    | true =>
      simp only [d12393, d162139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d162092 q = 1) : d162140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d162140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12263 q = 1) (hb : d162092 q = 1) : d12263 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12395 q = 1) (hb : d162092 q = 1) : d162141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d162141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12396 q = 1) (hb : d162092 q = 1) : d162142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12396, d162142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12397 q = 1) (hb : d162092 q = 1) : d162143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12397, d162143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12398 q = 1) (hb : d162092 q = 1) : d162144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12398, d162144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33114 (p : Pattern) (ha : d115302 p = 1) (hb : d162092 p = 1) : d162150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12267 q = 1) (hb : d162092 q = 1) : d12267 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12399 q = 1) (hb : d162092 q = 1) : d162145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33113 q ha hb
    | true =>
      simp only [d12399, d162145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115298 q = 1) (hb : d162092 q = 1) : d162146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115298, d162146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d162092 q = 1) : d12420 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d162092 q = 1) : d162147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115299, d162147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d162092 q = 1) : d162148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d162148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d162092 q = 1) : d162149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d162149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d162092 q = 1) : d162150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d162150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33115 (p : Pattern) (ha : d115308 p = 1) (hb : d162092 p = 1) : d162156 p = 1 := by
  have h0 (q : Pattern) (ha : d12299 q = 1) (hb : d162092 q = 1) : d12299 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115286 q = 1) (hb : d162092 q = 1) : d162121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33107 q ha hb
    | true =>
      simp only [d115286, d162121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33109 q ha hb
  have h2 (q : Pattern) (ha : d12374 q = 1) (hb : d162092 q = 1) : d12374 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115287 q = 1) (hb : d162092 q = 1) : d162122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115287, d162122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115288 q = 1) (hb : d162092 q = 1) : d162123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115288, d162123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115289 q = 1) (hb : d162092 q = 1) : d162124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115289, d162124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115293 q = 1) (hb : d162092 q = 1) : d162128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115293, d162128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33110 q ha hb
  have h8 (q : Pattern) (ha : d407 q = 1) (hb : d162092 q = 1) : d407 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115294 q = 1) (hb : d162092 q = 1) : d162129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115294, d162129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115295 q = 1) (hb : d162092 q = 1) : d162130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115295, d162130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115296 q = 1) (hb : d162092 q = 1) : d162131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115296, d162131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115297 q = 1) (hb : d162092 q = 1) : d162132 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115297, d162132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115303 q = 1) (hb : d162092 q = 1) : d162151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115303, d162151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33114 q ha hb
  have h14 (q : Pattern) (ha : d463 q = 1) (hb : d162092 q = 1) : d463 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115304 q = 1) (hb : d162092 q = 1) : d162152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115304, d162152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115305 q = 1) (hb : d162092 q = 1) : d162153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115305, d162153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115306 q = 1) (hb : d162092 q = 1) : d162154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115306, d162154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115307 q = 1) (hb : d162092 q = 1) : d162155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115307, d162155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115308 q = 1) (hb : d162092 q = 1) : d162156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115308, d162156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro33116 (p : Pattern) (ha : d115314 p = 1) (hb : d162092 p = 1) : d162162 p = 1 := by
  have h0 (q : Pattern) (ha : d115275 q = 1) (hb : d162092 q = 1) : d115275 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115309 q = 1) (hb : d162092 q = 1) : d162157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d162157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33115 q ha hb
  have h3 (q : Pattern) (ha : d115310 q = 1) (hb : d162092 q = 1) : d162158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d162158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115311 q = 1) (hb : d162092 q = 1) : d162159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d162159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115312 q = 1) (hb : d162092 q = 1) : d162160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d162160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115313 q = 1) (hb : d162092 q = 1) : d162161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d162161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115314 q = 1) (hb : d162092 q = 1) : d162162 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115314, d162162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33117 (p : Pattern) (ha : d12438 p = 1) (hb : d162092 p = 1) : d162164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4818 q = 1) (hb : d162092 q = 1) : d4818 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12313 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33104 q ha hb
    | true =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12314 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12315 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4821 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12316 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4822 q = 1) (hb : d162092 q = 1) : d4822 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12437 q = 1) (hb : d162092 q = 1) : d162163 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12437, d162163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12438 q = 1) (hb : d162092 q = 1) : d162164 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12438, d162164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33118 (p : Pattern) (ha : d12448 p = 1) (hb : d162092 p = 1) : d162170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d162092 q = 1) : d162169 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12448 q = 1) (hb : d162092 q = 1) : d162170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d162170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33119 (p : Pattern) (ha : d12458 p = 1) (hb : d162092 p = 1) : d162176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d162092 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33118 q ha hb
    | true =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12458 q = 1) (hb : d162092 q = 1) : d162176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33120 (p : Pattern) (ha : d12461 p = 1) (hb : d162092 p = 1) : d162179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d162092 q = 1) : d162169 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d162169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12461 q = 1) (hb : d162092 q = 1) : d162179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12461, d162179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33121 (p : Pattern) (ha : d12468 p = 1) (hb : d162092 p = 1) : d162185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d162092 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33118 q ha hb
    | true =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12462 q = 1) (hb : d162092 q = 1) : d12462 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12463 q = 1) (hb : d162092 q = 1) : d162180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33120 q ha hb
    | true =>
      simp only [d12463, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12464 q = 1) (hb : d162092 q = 1) : d162181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12465 q = 1) (hb : d162092 q = 1) : d162182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12465, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12466 q = 1) (hb : d162092 q = 1) : d162183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12467 q = 1) (hb : d162092 q = 1) : d162184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12468 q = 1) (hb : d162092 q = 1) : d162185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12468, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro33122 (p : Pattern) (ha : d12574 p = 1) (hb : d162092 p = 1) : d162250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d162092 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d162092 q = 1) : d162171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33118 q ha hb
    | true =>
      simp only [d12453, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d162092 q = 1) : d162172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d162092 q = 1) : d162173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d162092 q = 1) : d162174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d162092 q = 1) : d162175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12573 q = 1) (hb : d162092 q = 1) : d12573 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12574 q = 1) (hb : d162092 q = 1) : d162250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12574, d162250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33123 (p : Pattern) (ha : d12473 p = 1) (hb : d162092 p = 1) : d162190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d162092 q = 1) : d162189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12473 q = 1) (hb : d162092 q = 1) : d162190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d162190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33124 (p : Pattern) (ha : d12482 p = 1) (hb : d162092 p = 1) : d162197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d162092 q = 1) : d162195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d162092 q = 1) : d162196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12482 q = 1) (hb : d162092 q = 1) : d162197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d162197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33125 (p : Pattern) (ha : d12489 p = 1) (hb : d162092 p = 1) : d162202 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d547 q = 1) (hb : d162091 q = 1) : d162201 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d547, d162091, d162201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12489 q = 1) (hb : d162092 q = 1) : d162202 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12489, d162092, d162202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33126 (p : Pattern) (ha : d12502 p = 1) (hb : d162092 p = 1) : d162211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33125 q ha hb
    | true =>
      simp only [d12490, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33104 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12496 q = 1) (hb : d162092 q = 1) : d12496 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12497 q = 1) (hb : d162092 q = 1) : d162206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33104 q ha hb
    | true =>
      simp only [d12497, d162206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12498 q = 1) (hb : d162092 q = 1) : d162207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d162207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12499 q = 1) (hb : d162092 q = 1) : d162208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d162208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12500 q = 1) (hb : d162092 q = 1) : d162209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12500, d162209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4818 q = 1) (hb : d162092 q = 1) : d4818 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12313 q = 1) (hb : d162092 q = 1) : d162096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33104 q ha hb
    | true =>
      simp only [d12313, d162096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12314 q = 1) (hb : d162092 q = 1) : d162097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d162097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12315 q = 1) (hb : d162092 q = 1) : d162098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d162098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4821 q = 1) (hb : d162092 q = 1) : d4821 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d12316 q = 1) (hb : d162092 q = 1) : d162099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12316, d162099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12501 q = 1) (hb : d162092 q = 1) : d162210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12501, d162210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12502 q = 1) (hb : d162092 q = 1) : d162211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12502, d162211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro33127 (p : Pattern) (ha : d12508 p = 1) (hb : d162092 p = 1) : d162217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d162092 q = 1) : d162212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33126 q ha hb
    | true =>
      simp only [d12503, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d162092 q = 1) : d162213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d162092 q = 1) : d162214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d162092 q = 1) : d162215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d162092 q = 1) : d162216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d162092 q = 1) : d162217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d162217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33128 (p : Pattern) (ha : d12537 p = 1) (hb : d162092 p = 1) : d162223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d162092 q = 1) : d162220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d162092 q = 1) : d162221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d162092 q = 1) : d162222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d162092 q = 1) : d162223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d162223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33129 (p : Pattern) (ha : d115319 p = 1) (hb : d162092 p = 1) : d162229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d162092 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d162092 q = 1) : d162191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33123 q ha hb
    | true =>
      simp only [d12476, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d162092 q = 1) : d162192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d162092 q = 1) : d162193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d162092 q = 1) : d162194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d162092 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d162092 q = 1) : d162198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33124 q ha hb
    | true =>
      simp only [d12486, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d162092 q = 1) : d162199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d162092 q = 1) : d162200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d162092 q = 1) : d162218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33127 q ha hb
    | true =>
      simp only [d12509, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33118 q ha hb
  have h11 (q : Pattern) (ha : d115315 q = 1) (hb : d162092 q = 1) : d162219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115315, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d162092 q = 1) : d162224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33128 q ha hb
    | true =>
      simp only [d12538, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d162092 q = 1) : d162225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115316 q = 1) (hb : d162092 q = 1) : d162226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115317 q = 1) (hb : d162092 q = 1) : d162227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115317, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115318 q = 1) (hb : d162092 q = 1) : d162228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115318, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115319 q = 1) (hb : d162092 q = 1) : d162229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d162229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro33130 (p : Pattern) (ha : d12544 p = 1) (hb : d162092 p = 1) : d162230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d162092 q = 1) : d162168 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d162168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d162092 q = 1) : d162189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d162189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12544 q = 1) (hb : d162092 q = 1) : d162230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12544, d162230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33131 (p : Pattern) (ha : d12550 p = 1) (hb : d162092 p = 1) : d162235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d162092 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d162092 q = 1) : d162167 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d162167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d162092 q = 1) : d162195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d162195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d162092 q = 1) : d162196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d162196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12550 q = 1) (hb : d162092 q = 1) : d162235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12550, d162235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33132 (p : Pattern) (ha : d12555 p = 1) (hb : d162092 p = 1) : d162239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d162092 q = 1) : d162212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33126 q ha hb
    | true =>
      simp only [d12503, d162212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d162092 q = 1) : d162213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d162213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d162092 q = 1) : d162214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d162214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d162092 q = 1) : d162215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d162215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d162092 q = 1) : d162216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d162216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d162092 q = 1) : d162239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d162239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33133 (p : Pattern) (ha : d12561 p = 1) (hb : d162092 p = 1) : d162242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d162092 q = 1) : d162165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33117 q ha hb
    | true =>
      simp only [d12439, d162165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d162092 q = 1) : d162166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d162166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d162092 q = 1) : d162220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d162220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d162092 q = 1) : d162221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d162221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d162092 q = 1) : d162222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d162222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d162092 q = 1) : d162242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d162242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33134 (p : Pattern) (ha : d115324 p = 1) (hb : d162092 p = 1) : d162248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d162092 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d162092 q = 1) : d162191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33123 q ha hb
    | true =>
      simp only [d12476, d162191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d162092 q = 1) : d162192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d162192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d162092 q = 1) : d162193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d162193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d162092 q = 1) : d162194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d162194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d162092 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d162092 q = 1) : d162198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33124 q ha hb
    | true =>
      simp only [d12486, d162198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d162092 q = 1) : d162199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d162199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d162092 q = 1) : d162200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d162200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d162092 q = 1) : d162218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33127 q ha hb
    | true =>
      simp only [d12509, d162218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33118 q ha hb
  have h11 (q : Pattern) (ha : d115315 q = 1) (hb : d162092 q = 1) : d162219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115315, d162219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d162092 q = 1) : d162224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33128 q ha hb
    | true =>
      simp only [d12538, d162224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d162092 q = 1) : d162225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d162225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115316 q = 1) (hb : d162092 q = 1) : d162226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d162226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115317 q = 1) (hb : d162092 q = 1) : d162227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115317, d162227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115318 q = 1) (hb : d162092 q = 1) : d162228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115318, d162228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12545 q = 1) (hb : d162092 q = 1) : d12545 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12546 q = 1) (hb : d162092 q = 1) : d162231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33130 q ha hb
    | true =>
      simp only [d12546, d162231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12547 q = 1) (hb : d162092 q = 1) : d162232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d162232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12548 q = 1) (hb : d162092 q = 1) : d162233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12548, d162233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12549 q = 1) (hb : d162092 q = 1) : d162234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d162234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12551 q = 1) (hb : d162092 q = 1) : d12551 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12552 q = 1) (hb : d162092 q = 1) : d162236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33131 q ha hb
    | true =>
      simp only [d12552, d162236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12553 q = 1) (hb : d162092 q = 1) : d162237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d162237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12554 q = 1) (hb : d162092 q = 1) : d162238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12554, d162238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12556 q = 1) (hb : d162092 q = 1) : d162240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33132 q ha hb
    | true =>
      simp only [d12556, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33120 q ha hb
  have h27 (q : Pattern) (ha : d115320 q = 1) (hb : d162092 q = 1) : d162241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115320, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12562 q = 1) (hb : d162092 q = 1) : d162243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33133 q ha hb
    | true =>
      simp only [d12562, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12563 q = 1) (hb : d162092 q = 1) : d162244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12563, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115321 q = 1) (hb : d162092 q = 1) : d162245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115321, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115322 q = 1) (hb : d162092 q = 1) : d162246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115322, d162246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115323 q = 1) (hb : d162092 q = 1) : d162247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115323, d162247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115324 q = 1) (hb : d162092 q = 1) : d162248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115324, d162248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro33135 (p : Pattern) (ha : d115331 p = 1) (hb : d162092 p = 1) : d162257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d162092 q = 1) : d162240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33132 q ha hb
    | true =>
      simp only [d12556, d162240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33120 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d162092 q = 1) : d162241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d162241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d162092 q = 1) : d162243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33133 q ha hb
    | true =>
      simp only [d12562, d162243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d162092 q = 1) : d162244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d162244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d162092 q = 1) : d162245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d162245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d162092 q = 1) : d162255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d162255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d162092 q = 1) : d162256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d162256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d162092 q = 1) : d162257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d162257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33136 (p : Pattern) (ha : d12595 p = 1) (hb : d162092 p = 1) : d162264 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d663 q = 1) (hb : d162091 q = 1) : d162263 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d663, d162091, d162263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12595 q = 1) (hb : d162092 q = 1) : d162264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12595, d162092, d162264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33137 (p : Pattern) (ha : d12610 p = 1) (hb : d162092 p = 1) : d162273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33136 q ha hb
    | true =>
      simp only [d12596, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33111 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12604 q = 1) (hb : d162092 q = 1) : d12604 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12605 q = 1) (hb : d162092 q = 1) : d162268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33111 q ha hb
    | true =>
      simp only [d12605, d162268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12606 q = 1) (hb : d162092 q = 1) : d162269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d162269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12607 q = 1) (hb : d162092 q = 1) : d162270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d162270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12608 q = 1) (hb : d162092 q = 1) : d162271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12608, d162271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6078 q = 1) (hb : d162092 q = 1) : d6078 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12387 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33111 q ha hb
    | true =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12388 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12389 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6081 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d12390 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12609 q = 1) (hb : d162092 q = 1) : d162272 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12609, d162272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12610 q = 1) (hb : d162092 q = 1) : d162273 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12610, d162273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro33138 (p : Pattern) (ha : d12614 p = 1) (hb : d162092 p = 1) : d162277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6078 q = 1) (hb : d162092 q = 1) : d6078 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12387 q = 1) (hb : d162092 q = 1) : d162133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33111 q ha hb
    | true =>
      simp only [d12387, d162133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12388 q = 1) (hb : d162092 q = 1) : d162134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d162134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12389 q = 1) (hb : d162092 q = 1) : d162135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d162135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6081 q = 1) (hb : d162092 q = 1) : d6081 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12390 q = 1) (hb : d162092 q = 1) : d162136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12390, d162136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6082 q = 1) (hb : d162092 q = 1) : d6082 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12613 q = 1) (hb : d162092 q = 1) : d162276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12613, d162276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12614 q = 1) (hb : d162092 q = 1) : d162277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12614, d162277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33139 (p : Pattern) (ha : d12620 p = 1) (hb : d162092 p = 1) : d162283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d162092 q = 1) : d162274 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33137 q ha hb
    | true =>
      simp only [d12611, d162274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d162092 q = 1) : d162275 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d162275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33138 q ha hb
    | true =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d162092 q = 1) : d162280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d162280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d162092 q = 1) : d162281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d162281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d162092 q = 1) : d162282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d162282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d162092 q = 1) : d162283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d162283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33140 (p : Pattern) (ha : d12628 p = 1) (hb : d162092 p = 1) : d162287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33138 q ha hb
    | true =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12624 q = 1) (hb : d162092 q = 1) : d12624 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12625 q = 1) (hb : d162092 q = 1) : d162284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d162284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12626 q = 1) (hb : d162092 q = 1) : d162285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12626, d162285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12627 q = 1) (hb : d162092 q = 1) : d162286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12627, d162286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12628 q = 1) (hb : d162092 q = 1) : d162287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12628, d162287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33141 (p : Pattern) (ha : d12657 p = 1) (hb : d162092 p = 1) : d162293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d162092 q = 1) : d162278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33138 q ha hb
    | true =>
      simp only [d12615, d162278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d162092 q = 1) : d162279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d162279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d162092 q = 1) : d162290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d162290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d162092 q = 1) : d162291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d162291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d162092 q = 1) : d162292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d162292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d162092 q = 1) : d162293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d162293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33142 (p : Pattern) (ha : d115341 p = 1) (hb : d162092 p = 1) : d162299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d162092 q = 1) : d162288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33139 q ha hb
    | true =>
      simp only [d12629, d162288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33140 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d162092 q = 1) : d162289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d162289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d162092 q = 1) : d162294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33141 q ha hb
    | true =>
      simp only [d12658, d162294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d162092 q = 1) : d162295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d162295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d162092 q = 1) : d162296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d162296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d162092 q = 1) : d162297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d162297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d162092 q = 1) : d162298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d162298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d162092 q = 1) : d162299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d162299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33143 (p : Pattern) (ha : d115347 p = 1) (hb : d162092 p = 1) : d162305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d162092 q = 1) : d162177 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d162177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33119 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d162092 q = 1) : d162178 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d162178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d162092 q = 1) : d162186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33119 q ha hb
    | true =>
      simp only [d12469, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33121 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d162092 q = 1) : d162187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d162092 q = 1) : d162188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d162188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d162092 q = 1) : d162249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33129 q ha hb
    | true =>
      simp only [d115325, d162249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33134 q ha hb
  have h7 (q : Pattern) (ha : d12580 q = 1) (hb : d162092 q = 1) : d12580 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12581 q = 1) (hb : d162092 q = 1) : d162251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33122 q ha hb
    | true =>
      simp only [d12581, d162251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115326 q = 1) (hb : d162092 q = 1) : d162252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d162252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115327 q = 1) (hb : d162092 q = 1) : d162253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115327, d162253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115328 q = 1) (hb : d162092 q = 1) : d162254 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d162254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115332 q = 1) (hb : d162092 q = 1) : d162258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d162258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33135 q ha hb
  have h13 (q : Pattern) (ha : d12590 q = 1) (hb : d162092 q = 1) : d12590 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115333 q = 1) (hb : d162092 q = 1) : d162259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115333, d162259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115334 q = 1) (hb : d162092 q = 1) : d162260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115334, d162260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115335 q = 1) (hb : d162092 q = 1) : d162261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115335, d162261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115336 q = 1) (hb : d162092 q = 1) : d162262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115336, d162262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115342 q = 1) (hb : d162092 q = 1) : d162300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d162300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33142 q ha hb
  have h19 (q : Pattern) (ha : d12675 q = 1) (hb : d162092 q = 1) : d12675 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115343 q = 1) (hb : d162092 q = 1) : d162301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115343, d162301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115344 q = 1) (hb : d162092 q = 1) : d162302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115344, d162302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115345 q = 1) (hb : d162092 q = 1) : d162303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115345, d162303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115346 q = 1) (hb : d162092 q = 1) : d162304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115346, d162304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115347 q = 1) (hb : d162092 q = 1) : d162305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115347, d162305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro33144 (p : Pattern) (ha : d115353 p = 1) (hb : d162092 p = 1) : d162311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d162092 q = 1) : d162306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d162306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33143 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d162092 q = 1) : d162307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d162307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d162092 q = 1) : d162308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d162308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d162092 q = 1) : d162309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d162309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d162092 q = 1) : d162310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d162310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d162092 q = 1) : d162311 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d162311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33145 (p : Pattern) (ha : d12693 p = 1) (hb : d162092 p = 1) : d162315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4913 q = 1) (hb : d162092 q = 1) : d4913 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12688 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33125 q ha hb
    | true =>
      simp only [d12688, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12689 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12690 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4916 q = 1) (hb : d162092 q = 1) : d4916 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12691 q = 1) (hb : d162092 q = 1) : d162313 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12691, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4917 q = 1) (hb : d162092 q = 1) : d4917 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12692 q = 1) (hb : d162092 q = 1) : d162314 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12692, d162314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12693 q = 1) (hb : d162092 q = 1) : d162315 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12693, d162315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33146 (p : Pattern) (ha : d12703 p = 1) (hb : d162092 p = 1) : d162321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d162092 q = 1) : d162320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12703 q = 1) (hb : d162092 q = 1) : d162321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d162321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33147 (p : Pattern) (ha : d12713 p = 1) (hb : d162092 p = 1) : d162327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d162092 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33146 q ha hb
    | true =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12713 q = 1) (hb : d162092 q = 1) : d162327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33148 (p : Pattern) (ha : d12716 p = 1) (hb : d162092 p = 1) : d162330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d162092 q = 1) : d162320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d162320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12716 q = 1) (hb : d162092 q = 1) : d162330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12716, d162330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33149 (p : Pattern) (ha : d12723 p = 1) (hb : d162092 p = 1) : d162336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d162092 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33146 q ha hb
    | true =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12717 q = 1) (hb : d162092 q = 1) : d12717 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12718 q = 1) (hb : d162092 q = 1) : d162331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33148 q ha hb
    | true =>
      simp only [d12718, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12719 q = 1) (hb : d162092 q = 1) : d162332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12720 q = 1) (hb : d162092 q = 1) : d162333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12720, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12721 q = 1) (hb : d162092 q = 1) : d162334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12722 q = 1) (hb : d162092 q = 1) : d162335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12723 q = 1) (hb : d162092 q = 1) : d162336 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12723, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro33150 (p : Pattern) (ha : d12833 p = 1) (hb : d162092 p = 1) : d162401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d162092 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d162092 q = 1) : d162322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33146 q ha hb
    | true =>
      simp only [d12708, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d162092 q = 1) : d162323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d162092 q = 1) : d162324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d162092 q = 1) : d162325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d162092 q = 1) : d162326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12832 q = 1) (hb : d162092 q = 1) : d12832 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12833 q = 1) (hb : d162092 q = 1) : d162401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12833, d162401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33151 (p : Pattern) (ha : d12728 p = 1) (hb : d162092 p = 1) : d162341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d162092 q = 1) : d162340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12728 q = 1) (hb : d162092 q = 1) : d162341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d162341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33152 (p : Pattern) (ha : d12737 p = 1) (hb : d162092 p = 1) : d162348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d162092 q = 1) : d162346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d162092 q = 1) : d162347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12737 q = 1) (hb : d162092 q = 1) : d162348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d162348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro33153 (p : Pattern) (ha : d12744 p = 1) (hb : d162092 p = 1) : d162353 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d837 q = 1) : d837 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d838 q = 1) (hb : d162091 q = 1) : d162352 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d162091, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d838, d162091, d162352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12744 q = 1) (hb : d162092 q = 1) : d162353 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d162092, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12744, d162092, d162353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33154 (p : Pattern) (ha : d12757 p = 1) (hb : d162092 p = 1) : d162362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d162092 q = 1) : d162354 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33153 q ha hb
    | true =>
      simp only [d12745, d162354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33125 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d162092 q = 1) : d162355 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d162355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d162092 q = 1) : d162356 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d162356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12751 q = 1) (hb : d162092 q = 1) : d12751 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12752 q = 1) (hb : d162092 q = 1) : d162357 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33125 q ha hb
    | true =>
      simp only [d12752, d162357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12753 q = 1) (hb : d162092 q = 1) : d162358 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d162358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12754 q = 1) (hb : d162092 q = 1) : d162359 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d162359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12755 q = 1) (hb : d162092 q = 1) : d162360 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12755, d162360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4913 q = 1) (hb : d162092 q = 1) : d4913 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12688 q = 1) (hb : d162092 q = 1) : d162203 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33125 q ha hb
    | true =>
      simp only [d12688, d162203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12689 q = 1) (hb : d162092 q = 1) : d162204 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d162204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12690 q = 1) (hb : d162092 q = 1) : d162205 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d162205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4916 q = 1) (hb : d162092 q = 1) : d4916 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d12691 q = 1) (hb : d162092 q = 1) : d162313 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12691, d162313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12756 q = 1) (hb : d162092 q = 1) : d162361 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12756, d162361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12757 q = 1) (hb : d162092 q = 1) : d162362 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12757, d162362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro33155 (p : Pattern) (ha : d12763 p = 1) (hb : d162092 p = 1) : d162368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d162092 q = 1) : d162363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33154 q ha hb
    | true =>
      simp only [d12758, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d162092 q = 1) : d162364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d162092 q = 1) : d162365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d162092 q = 1) : d162366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d162092 q = 1) : d162367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d162092 q = 1) : d162368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d162368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33156 (p : Pattern) (ha : d12796 p = 1) (hb : d162092 p = 1) : d162374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d162092 q = 1) : d162371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d162092 q = 1) : d162372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d162092 q = 1) : d162373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d162092 q = 1) : d162374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d162374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33157 (p : Pattern) (ha : d115359 p = 1) (hb : d162092 p = 1) : d162380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d162092 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d162092 q = 1) : d162342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33151 q ha hb
    | true =>
      simp only [d12731, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d162092 q = 1) : d162343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d162092 q = 1) : d162344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d162092 q = 1) : d162345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d162092 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d162092 q = 1) : d162349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33152 q ha hb
    | true =>
      simp only [d12741, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d162092 q = 1) : d162350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d162092 q = 1) : d162351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d162092 q = 1) : d162369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33155 q ha hb
    | true =>
      simp only [d12764, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33146 q ha hb
  have h11 (q : Pattern) (ha : d115355 q = 1) (hb : d162092 q = 1) : d162370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115355, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d162092 q = 1) : d162375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33156 q ha hb
    | true =>
      simp only [d12797, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d162092 q = 1) : d162376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115356 q = 1) (hb : d162092 q = 1) : d162377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115357 q = 1) (hb : d162092 q = 1) : d162378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115357, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115358 q = 1) (hb : d162092 q = 1) : d162379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115358, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115359 q = 1) (hb : d162092 q = 1) : d162380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d162380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro33158 (p : Pattern) (ha : d12803 p = 1) (hb : d162092 p = 1) : d162381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d162092 q = 1) : d162319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d162319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d162092 q = 1) : d162340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d162340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12803 q = 1) (hb : d162092 q = 1) : d162381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12803, d162381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33159 (p : Pattern) (ha : d12809 p = 1) (hb : d162092 p = 1) : d162386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d162092 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d162092 q = 1) : d162318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d162318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d162092 q = 1) : d162346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d162346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d162092 q = 1) : d162347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d162347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12809 q = 1) (hb : d162092 q = 1) : d162386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12809, d162386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33160 (p : Pattern) (ha : d12814 p = 1) (hb : d162092 p = 1) : d162390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d162092 q = 1) : d162363 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33154 q ha hb
    | true =>
      simp only [d12758, d162363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d162092 q = 1) : d162364 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d162364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d162092 q = 1) : d162365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d162365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d162092 q = 1) : d162366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d162366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d162092 q = 1) : d162367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d162367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d162092 q = 1) : d162390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d162390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33161 (p : Pattern) (ha : d12820 p = 1) (hb : d162092 p = 1) : d162393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d162092 q = 1) : d162316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33145 q ha hb
    | true =>
      simp only [d12694, d162316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d162092 q = 1) : d162317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d162317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d162092 q = 1) : d162371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d162371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d162092 q = 1) : d162372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d162372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d162092 q = 1) : d162373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d162373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d162092 q = 1) : d162393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d162393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33162 (p : Pattern) (ha : d115364 p = 1) (hb : d162092 p = 1) : d162399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d162092 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d162092 q = 1) : d162342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33151 q ha hb
    | true =>
      simp only [d12731, d162342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d162092 q = 1) : d162343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d162343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d162092 q = 1) : d162344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d162344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d162092 q = 1) : d162345 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d162345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d162092 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d162092 q = 1) : d162349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33152 q ha hb
    | true =>
      simp only [d12741, d162349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d162092 q = 1) : d162350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d162350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d162092 q = 1) : d162351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d162351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d162092 q = 1) : d162369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33155 q ha hb
    | true =>
      simp only [d12764, d162369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33146 q ha hb
  have h11 (q : Pattern) (ha : d115355 q = 1) (hb : d162092 q = 1) : d162370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115355, d162370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d162092 q = 1) : d162375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33156 q ha hb
    | true =>
      simp only [d12797, d162375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d162092 q = 1) : d162376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d162376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115356 q = 1) (hb : d162092 q = 1) : d162377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d162377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115357 q = 1) (hb : d162092 q = 1) : d162378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115357, d162378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115358 q = 1) (hb : d162092 q = 1) : d162379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115358, d162379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12804 q = 1) (hb : d162092 q = 1) : d12804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12805 q = 1) (hb : d162092 q = 1) : d162382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33158 q ha hb
    | true =>
      simp only [d12805, d162382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12806 q = 1) (hb : d162092 q = 1) : d162383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d162383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12807 q = 1) (hb : d162092 q = 1) : d162384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12807, d162384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12808 q = 1) (hb : d162092 q = 1) : d162385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d162385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12810 q = 1) (hb : d162092 q = 1) : d12810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12811 q = 1) (hb : d162092 q = 1) : d162387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33159 q ha hb
    | true =>
      simp only [d12811, d162387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12812 q = 1) (hb : d162092 q = 1) : d162388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d162388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12813 q = 1) (hb : d162092 q = 1) : d162389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12813, d162389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12815 q = 1) (hb : d162092 q = 1) : d162391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33160 q ha hb
    | true =>
      simp only [d12815, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33148 q ha hb
  have h27 (q : Pattern) (ha : d115360 q = 1) (hb : d162092 q = 1) : d162392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115360, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12821 q = 1) (hb : d162092 q = 1) : d162394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33161 q ha hb
    | true =>
      simp only [d12821, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12822 q = 1) (hb : d162092 q = 1) : d162395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12822, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115361 q = 1) (hb : d162092 q = 1) : d162396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115361, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115362 q = 1) (hb : d162092 q = 1) : d162397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115362, d162397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115363 q = 1) (hb : d162092 q = 1) : d162398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115363, d162398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115364 q = 1) (hb : d162092 q = 1) : d162399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115364, d162399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro33163 (p : Pattern) (ha : d115371 p = 1) (hb : d162092 p = 1) : d162408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d162092 q = 1) : d162391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33160 q ha hb
    | true =>
      simp only [d12815, d162391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33148 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d162092 q = 1) : d162392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d162392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d162092 q = 1) : d162394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33161 q ha hb
    | true =>
      simp only [d12821, d162394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d162092 q = 1) : d162395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d162395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d162092 q = 1) : d162396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d162396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d162092 q = 1) : d162406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d162406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d162092 q = 1) : d162407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d162407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d162092 q = 1) : d162408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d162408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33164 (p : Pattern) (ha : d12854 p = 1) (hb : d162092 p = 1) : d162415 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d968 q = 1) : d968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h3 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d969 q = 1) (hb : d162091 q = 1) : d162414 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d162091, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d969, d162091, d162414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12854 q = 1) (hb : d162092 q = 1) : d162415 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d162092, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12854, d162092, d162415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33165 (p : Pattern) (ha : d12873 p = 1) (hb : d162092 p = 1) : d162425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d162092 q = 1) : d162416 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33164 q ha hb
    | true =>
      simp only [d12855, d162416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33136 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d162092 q = 1) : d162417 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d162417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d162092 q = 1) : d162418 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d162418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12863 q = 1) (hb : d162092 q = 1) : d12863 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12864 q = 1) (hb : d162092 q = 1) : d162419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33136 q ha hb
    | true =>
      simp only [d12864, d162419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12865 q = 1) (hb : d162092 q = 1) : d162420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d162420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12866 q = 1) (hb : d162092 q = 1) : d162421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d162421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12867 q = 1) (hb : d162092 q = 1) : d162422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12867, d162422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6210 q = 1) (hb : d162092 q = 1) : d6210 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12868 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33136 q ha hb
    | true =>
      simp only [d12868, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12869 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12870 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6213 q = 1) (hb : d162092 q = 1) : d6213 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d12871 q = 1) (hb : d162092 q = 1) : d162423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12871, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12872 q = 1) (hb : d162092 q = 1) : d162424 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12872, d162424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12873 q = 1) (hb : d162092 q = 1) : d162425 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12873, d162425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro33166 (p : Pattern) (ha : d12877 p = 1) (hb : d162092 p = 1) : d162429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6210 q = 1) (hb : d162092 q = 1) : d6210 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12868 q = 1) (hb : d162092 q = 1) : d162265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33136 q ha hb
    | true =>
      simp only [d12868, d162265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12869 q = 1) (hb : d162092 q = 1) : d162266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d162266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12870 q = 1) (hb : d162092 q = 1) : d162267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d162267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6213 q = 1) (hb : d162092 q = 1) : d6213 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12871 q = 1) (hb : d162092 q = 1) : d162423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12871, d162423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6214 q = 1) (hb : d162092 q = 1) : d6214 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12876 q = 1) (hb : d162092 q = 1) : d162428 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12876, d162428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12877 q = 1) (hb : d162092 q = 1) : d162429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12877, d162429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro33167 (p : Pattern) (ha : d12883 p = 1) (hb : d162092 p = 1) : d162435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d162092 q = 1) : d162426 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33165 q ha hb
    | true =>
      simp only [d12874, d162426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d162092 q = 1) : d162427 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d162427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33166 q ha hb
    | true =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d162092 q = 1) : d162432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d162432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d162092 q = 1) : d162433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d162433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d162092 q = 1) : d162434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d162434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d162092 q = 1) : d162435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d162435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33168 (p : Pattern) (ha : d12891 p = 1) (hb : d162092 p = 1) : d162439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33166 q ha hb
    | true =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12887 q = 1) (hb : d162092 q = 1) : d12887 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12888 q = 1) (hb : d162092 q = 1) : d162436 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d162436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12889 q = 1) (hb : d162092 q = 1) : d162437 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12889, d162437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12890 q = 1) (hb : d162092 q = 1) : d162438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12890, d162438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12891 q = 1) (hb : d162092 q = 1) : d162439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12891, d162439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33169 (p : Pattern) (ha : d12924 p = 1) (hb : d162092 p = 1) : d162445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d162092 q = 1) : d162430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33166 q ha hb
    | true =>
      simp only [d12878, d162430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d162092 q = 1) : d162431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d162431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d162092 q = 1) : d162442 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d162442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d162092 q = 1) : d162443 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d162443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d162092 q = 1) : d162444 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d162444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d162092 q = 1) : d162445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d162445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33170 (p : Pattern) (ha : d115381 p = 1) (hb : d162092 p = 1) : d162451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d162092 q = 1) : d162440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33167 q ha hb
    | true =>
      simp only [d12892, d162440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33168 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d162092 q = 1) : d162441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d162441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d162092 q = 1) : d162446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33169 q ha hb
    | true =>
      simp only [d12925, d162446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d162092 q = 1) : d162447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d162447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d162092 q = 1) : d162448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d162448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d162092 q = 1) : d162449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d162449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d162092 q = 1) : d162450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d162450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d162092 q = 1) : d162451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d162451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33171 (p : Pattern) (ha : d115387 p = 1) (hb : d162092 p = 1) : d162457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d162092 q = 1) : d162328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d162328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33147 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d162092 q = 1) : d162329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d162329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d162092 q = 1) : d162337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33147 q ha hb
    | true =>
      simp only [d12724, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33149 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d162092 q = 1) : d162338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d162092 q = 1) : d162339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d162339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d162092 q = 1) : d162400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33157 q ha hb
    | true =>
      simp only [d115365, d162400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33162 q ha hb
  have h7 (q : Pattern) (ha : d12839 q = 1) (hb : d162092 q = 1) : d12839 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12840 q = 1) (hb : d162092 q = 1) : d162402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33150 q ha hb
    | true =>
      simp only [d12840, d162402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115366 q = 1) (hb : d162092 q = 1) : d162403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d162403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115367 q = 1) (hb : d162092 q = 1) : d162404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115367, d162404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115368 q = 1) (hb : d162092 q = 1) : d162405 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d162405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115372 q = 1) (hb : d162092 q = 1) : d162409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d162409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33163 q ha hb
  have h13 (q : Pattern) (ha : d12849 q = 1) (hb : d162092 q = 1) : d12849 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115373 q = 1) (hb : d162092 q = 1) : d162410 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115373, d162410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115374 q = 1) (hb : d162092 q = 1) : d162411 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115374, d162411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115375 q = 1) (hb : d162092 q = 1) : d162412 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115375, d162412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115376 q = 1) (hb : d162092 q = 1) : d162413 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115376, d162413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115382 q = 1) (hb : d162092 q = 1) : d162452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d162452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33170 q ha hb
  have h19 (q : Pattern) (ha : d12942 q = 1) (hb : d162092 q = 1) : d12942 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115383 q = 1) (hb : d162092 q = 1) : d162453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115383, d162453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115384 q = 1) (hb : d162092 q = 1) : d162454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115384, d162454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115385 q = 1) (hb : d162092 q = 1) : d162455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115385, d162455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115386 q = 1) (hb : d162092 q = 1) : d162456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115386, d162456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115387 q = 1) (hb : d162092 q = 1) : d162457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115387, d162457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro33172 (p : Pattern) (ha : d115393 p = 1) (hb : d162092 p = 1) : d162463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d162092 q = 1) : d162458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d162458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33171 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d162092 q = 1) : d162459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d162459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d162092 q = 1) : d162460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d162460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d162092 q = 1) : d162461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d162461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d162092 q = 1) : d162462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d162462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d162092 q = 1) : d162463 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d162463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33173 (p : Pattern) (ha : d5009 p = 1) (hb : d162092 p = 1) : d162469 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1113 q = 1) : d1113 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1125 q = 1) (hb : d162091 q = 1) : d162468 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d162091, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d162091, d162468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5009 q = 1) (hb : d162092 q = 1) : d162469 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d162092, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5009, d162092, d162469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33174 (p : Pattern) (ha : d12956 p = 1) (hb : d162092 p = 1) : d162467 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1103 q = 1) : d1103 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1114 q = 1) (hb : d162091 q = 1) : d162466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d162091, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1114, d162091, d162466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12956 q = 1) (hb : d162092 q = 1) : d162467 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d162092, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12956, d162092, d162467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33175 (p : Pattern) (ha : d12967 p = 1) (hb : d162092 p = 1) : d162482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33174 q ha hb
    | true =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5023 q = 1) (hb : d162092 q = 1) : d5023 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5024 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
    | true =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5025 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5026 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12960 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12961 q = 1) (hb : d162092 q = 1) : d12961 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12962 q = 1) (hb : d162092 q = 1) : d162477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
    | true =>
      simp only [d12962, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12963 q = 1) (hb : d162092 q = 1) : d162478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12964 q = 1) (hb : d162092 q = 1) : d162479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12965 q = 1) (hb : d162092 q = 1) : d162480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12965, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d12966 q = 1) (hb : d162092 q = 1) : d162481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12966, d162481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12967 q = 1) (hb : d162092 q = 1) : d162482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12967, d162482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro33176 (p : Pattern) (ha : d12971 p = 1) (hb : d162092 p = 1) : d162486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12961 q = 1) (hb : d162092 q = 1) : d12961 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12962 q = 1) (hb : d162092 q = 1) : d162477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
    | true =>
      simp only [d12962, d162477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12963 q = 1) (hb : d162092 q = 1) : d162478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d162478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12964 q = 1) (hb : d162092 q = 1) : d162479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d162479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12965 q = 1) (hb : d162092 q = 1) : d162480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12965, d162480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12970 q = 1) (hb : d162092 q = 1) : d162485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12970, d162485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12971 q = 1) (hb : d162092 q = 1) : d162486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12971, d162486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33177 (p : Pattern) (ha : d12977 p = 1) (hb : d162092 p = 1) : d162492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d162092 q = 1) : d162491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d162092 q = 1) : d162492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d162492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33178 (p : Pattern) (ha : d12981 p = 1) (hb : d162092 p = 1) : d162496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d162092 q = 1) : d162495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d162092 q = 1) : d162496 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d162496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33179 (p : Pattern) (ha : d12987 p = 1) (hb : d162092 p = 1) : d162502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d162092 q = 1) : d162497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33177 q ha hb
    | true =>
      simp only [d12982, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33178 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d162092 q = 1) : d162498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d162092 q = 1) : d162499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d162092 q = 1) : d162500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d162092 q = 1) : d162501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d162092 q = 1) : d162502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33180 (p : Pattern) (ha : d12990 p = 1) (hb : d162092 p = 1) : d162505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d162092 q = 1) : d162491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d162491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d162092 q = 1) : d162505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d162505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33181 (p : Pattern) (ha : d12991 p = 1) (hb : d162092 p = 1) : d162506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d162092 q = 1) : d162495 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d162495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d162092 q = 1) : d162506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d162506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33182 (p : Pattern) (ha : d12997 p = 1) (hb : d162092 p = 1) : d162512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d162092 q = 1) : d162497 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33177 q ha hb
    | true =>
      simp only [d12982, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33178 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d162092 q = 1) : d162498 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d162092 q = 1) : d162499 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d162092 q = 1) : d162500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d162092 q = 1) : d162501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d162092 q = 1) : d162507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33180 q ha hb
    | true =>
      simp only [d12992, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33181 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d162092 q = 1) : d162508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d162092 q = 1) : d162509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d162092 q = 1) : d162510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d162092 q = 1) : d162511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d162092 q = 1) : d162512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33183 (p : Pattern) (ha : d13040 p = 1) (hb : d162092 p = 1) : d162548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33174 q ha hb
    | true =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5023 q = 1) (hb : d162092 q = 1) : d5023 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5024 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
    | true =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5025 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5026 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12960 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5027 q = 1) (hb : d162092 q = 1) : d162546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5027, d162546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13039 q = 1) (hb : d162092 q = 1) : d162547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13039, d162547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13040 q = 1) (hb : d162092 q = 1) : d162548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13040, d162548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro33184 (p : Pattern) (ha : d13050 p = 1) (hb : d162092 p = 1) : d162558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33183 q ha hb
    | true =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d162092 q = 1) : d162555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d162092 q = 1) : d162556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d162092 q = 1) : d162557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d162092 q = 1) : d162558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d162558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33185 (p : Pattern) (ha : d13134 p = 1) (hb : d162092 p = 1) : d162604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d162092 q = 1) : d162594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33184 q ha hb
    | true =>
      simp only [d13124, d162594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33178 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d162092 q = 1) : d162595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d162595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d162092 q = 1) : d162596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d162596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d162092 q = 1) : d162597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d162597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d162092 q = 1) : d162598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d162598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d162092 q = 1) : d162599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33178 q ha hb
    | true =>
      simp only [d13129, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d162092 q = 1) : d162600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d162092 q = 1) : d162601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d162092 q = 1) : d162602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d162092 q = 1) : d162603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d162092 q = 1) : d162604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d162604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33186 (p : Pattern) (ha : d13140 p = 1) (hb : d162092 p = 1) : d162610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d162092 q = 1) : d162599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33178 q ha hb
    | true =>
      simp only [d13129, d162599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d162092 q = 1) : d162600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d162600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d162092 q = 1) : d162601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d162601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d162092 q = 1) : d162602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d162602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d162092 q = 1) : d162603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d162603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d162092 q = 1) : d162605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33181 q ha hb
    | true =>
      simp only [d13135, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d162092 q = 1) : d162606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d162092 q = 1) : d162607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d162092 q = 1) : d162608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d162092 q = 1) : d162609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d162092 q = 1) : d162610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d162610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33187 (p : Pattern) (ha : d13149 p = 1) (hb : d162092 p = 1) : d162619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d162092 q = 1) : d162605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33181 q ha hb
    | true =>
      simp only [d13135, d162605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d162092 q = 1) : d162606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d162606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d162092 q = 1) : d162607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d162607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d162092 q = 1) : d162608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d162608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d162092 q = 1) : d162609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d162609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d162092 q = 1) : d162619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d162619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33188 (p : Pattern) (ha : d6349 p = 1) (hb : d162092 p = 1) : d162637 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1388 q = 1) : d1388 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1395 q = 1) (hb : d162091 q = 1) : d162636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d162091, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1395, d162091, d162636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6349 q = 1) (hb : d162092 q = 1) : d162637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d162092, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6349, d162092, d162637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33189 (p : Pattern) (ha : d13196 p = 1) (hb : d162092 p = 1) : d162663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13190 q = 1) (hb : d162092 q = 1) : d13190 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13191 q = 1) (hb : d162092 q = 1) : d162658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
    | true =>
      simp only [d13191, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13192 q = 1) (hb : d162092 q = 1) : d162659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13193 q = 1) (hb : d162092 q = 1) : d162660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13194 q = 1) (hb : d162092 q = 1) : d162661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13194, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13195 q = 1) (hb : d162092 q = 1) : d162662 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13195, d162662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13196 q = 1) (hb : d162092 q = 1) : d162663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13196, d162663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33190 (p : Pattern) (ha : d13260 p = 1) (hb : d162092 p = 1) : d162690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33189 q ha hb
    | true =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d162092 q = 1) : d162687 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d162687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d162092 q = 1) : d162688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d162688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d162092 q = 1) : d162689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d162689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d162092 q = 1) : d162690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d162690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33191 (p : Pattern) (ha : d13266 p = 1) (hb : d162092 p = 1) : d162696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d162092 q = 1) : d162691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33190 q ha hb
    | true =>
      simp only [d13261, d162691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d162092 q = 1) : d162692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d162692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d162092 q = 1) : d162693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d162693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d162092 q = 1) : d162694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d162694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d162092 q = 1) : d162695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d162695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d162092 q = 1) : d162696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d162696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33192 (p : Pattern) (ha : d13002 p = 1) (hb : d162092 p = 1) : d162517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d162092 q = 1) : d162516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d162092 q = 1) : d162517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d162517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33193 (p : Pattern) (ha : d13004 p = 1) (hb : d162092 p = 1) : d162519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d162092 q = 1) : d162518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d162092 q = 1) : d162519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d162519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33194 (p : Pattern) (ha : d13011 p = 1) (hb : d162092 p = 1) : d162526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d162092 q = 1) : d162524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d162092 q = 1) : d162525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d162092 q = 1) : d162526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d162526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33195 (p : Pattern) (ha : d13014 p = 1) (hb : d162092 p = 1) : d162529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d162092 q = 1) : d162527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d162092 q = 1) : d162528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d162092 q = 1) : d162529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d162529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33196 (p : Pattern) (ha : d13018 p = 1) (hb : d162092 p = 1) : d162534 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1213 q = 1) : d1213 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1214 q = 1) (hb : d162091 q = 1) : d162533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d162091, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1214, d162091, d162533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13018 q = 1) (hb : d162092 q = 1) : d162534 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d162092, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13018, d162092, d162534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33197 (p : Pattern) (ha : d13036 p = 1) (hb : d162092 p = 1) : d162543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d162092 q = 1) : d162535 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33196 q ha hb
    | true =>
      simp only [d13019, d162535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33174 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d162092 q = 1) : d162536 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d162536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d162092 q = 1) : d162537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d162537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13030 q = 1) (hb : d162092 q = 1) : d13030 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13031 q = 1) (hb : d162092 q = 1) : d162538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33174 q ha hb
    | true =>
      simp only [d13031, d162538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13032 q = 1) (hb : d162092 q = 1) : d162539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d162539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13033 q = 1) (hb : d162092 q = 1) : d162540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d162540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13034 q = 1) (hb : d162092 q = 1) : d162541 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13034, d162541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12957 q = 1) (hb : d162092 q = 1) : d162470 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33174 q ha hb
    | true =>
      simp only [d12957, d162470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
  have h10 (q : Pattern) (ha : d12958 q = 1) (hb : d162092 q = 1) : d162471 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d162471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12959 q = 1) (hb : d162092 q = 1) : d162472 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d162472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5023 q = 1) (hb : d162092 q = 1) : d5023 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5024 q = 1) (hb : d162092 q = 1) : d162473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33173 q ha hb
    | true =>
      simp only [d5024, d162473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5025 q = 1) (hb : d162092 q = 1) : d162474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d162474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5026 q = 1) (hb : d162092 q = 1) : d162475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d162475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12960 q = 1) (hb : d162092 q = 1) : d162476 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12960, d162476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13035 q = 1) (hb : d162092 q = 1) : d162542 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13035, d162542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13036 q = 1) (hb : d162092 q = 1) : d162543 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13036, d162543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro33198 (p : Pattern) (ha : d13046 p = 1) (hb : d162092 p = 1) : d162554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d162092 q = 1) : d162544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33197 q ha hb
    | true =>
      simp only [d13037, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d162092 q = 1) : d162545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33183 q ha hb
    | true =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d162092 q = 1) : d162551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d162092 q = 1) : d162552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d162092 q = 1) : d162553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d162092 q = 1) : d162554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d162554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33199 (p : Pattern) (ha : d13091 p = 1) (hb : d162092 p = 1) : d162564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d162092 q = 1) : d162561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d162092 q = 1) : d162562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d162092 q = 1) : d162563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d162092 q = 1) : d162564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d162564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33200 (p : Pattern) (ha : d115400 p = 1) (hb : d162092 p = 1) : d162570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d162092 q = 1) : d162520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33192 q ha hb
    | true =>
      simp only [d13005, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33193 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d162092 q = 1) : d162521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d162092 q = 1) : d162522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d162092 q = 1) : d162523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d162092 q = 1) : d162530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33194 q ha hb
    | true =>
      simp only [d13015, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33195 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d162092 q = 1) : d162531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d162092 q = 1) : d162532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d162092 q = 1) : d162559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33198 q ha hb
    | true =>
      simp only [d13051, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33184 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d162092 q = 1) : d162560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d162092 q = 1) : d162565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33199 q ha hb
    | true =>
      simp only [d13092, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d162092 q = 1) : d162566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d162092 q = 1) : d162567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d162092 q = 1) : d162568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d162092 q = 1) : d162569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d162092 q = 1) : d162570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d162570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33201 (p : Pattern) (ha : d13098 p = 1) (hb : d162092 p = 1) : d162571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d162092 q = 1) : d162490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d162490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d162092 q = 1) : d162516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d162516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d162092 q = 1) : d162571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d162571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33202 (p : Pattern) (ha : d13099 p = 1) (hb : d162092 p = 1) : d162572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d162092 q = 1) : d162494 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d162494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d162092 q = 1) : d162518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d162518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d162092 q = 1) : d162572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d162572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33203 (p : Pattern) (ha : d13104 p = 1) (hb : d162092 p = 1) : d162577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d162092 q = 1) : d162489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d162489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d162092 q = 1) : d162524 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d162524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d162092 q = 1) : d162525 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d162525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d162092 q = 1) : d162577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d162577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33204 (p : Pattern) (ha : d13105 p = 1) (hb : d162092 p = 1) : d162578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d162092 q = 1) : d162493 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d162493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d162092 q = 1) : d162527 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d162527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d162092 q = 1) : d162528 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d162528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d162092 q = 1) : d162578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d162578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33205 (p : Pattern) (ha : d13109 p = 1) (hb : d162092 p = 1) : d162582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d162092 q = 1) : d162544 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33197 q ha hb
    | true =>
      simp only [d13037, d162544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d162092 q = 1) : d162545 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d162545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33183 q ha hb
    | true =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d162092 q = 1) : d162551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d162551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d162092 q = 1) : d162552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d162552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d162092 q = 1) : d162553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d162553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d162092 q = 1) : d162582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d162582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33206 (p : Pattern) (ha : d13110 p = 1) (hb : d162092 p = 1) : d162583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d162092 q = 1) : d162549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33183 q ha hb
    | true =>
      simp only [d13041, d162549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d162092 q = 1) : d162550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d162550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d162092 q = 1) : d162487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33176 q ha hb
    | true =>
      simp only [d12972, d162487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d162092 q = 1) : d162488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d162488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d162092 q = 1) : d162555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d162555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d162092 q = 1) : d162556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d162556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d162092 q = 1) : d162557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d162557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d162092 q = 1) : d162583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d162583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33207 (p : Pattern) (ha : d13116 p = 1) (hb : d162092 p = 1) : d162586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d162092 q = 1) : d162483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33175 q ha hb
    | true =>
      simp only [d12968, d162483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d162092 q = 1) : d162484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d162484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d162092 q = 1) : d162561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d162561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d162092 q = 1) : d162562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d162562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d162092 q = 1) : d162563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d162563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d162092 q = 1) : d162586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d162586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33208 (p : Pattern) (ha : d115405 p = 1) (hb : d162092 p = 1) : d162592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d162092 q = 1) : d162520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33192 q ha hb
    | true =>
      simp only [d13005, d162520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33193 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d162092 q = 1) : d162521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d162521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d162092 q = 1) : d162522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d162522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d162092 q = 1) : d162523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d162523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d162092 q = 1) : d162530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33194 q ha hb
    | true =>
      simp only [d13015, d162530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33195 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d162092 q = 1) : d162531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d162531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d162092 q = 1) : d162532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d162532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d162092 q = 1) : d162559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33198 q ha hb
    | true =>
      simp only [d13051, d162559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33184 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d162092 q = 1) : d162560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d162560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d162092 q = 1) : d162565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33199 q ha hb
    | true =>
      simp only [d13092, d162565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d162092 q = 1) : d162566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d162566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d162092 q = 1) : d162567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d162567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d162092 q = 1) : d162568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d162568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d162092 q = 1) : d162569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d162569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d162092 q = 1) : d162573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33201 q ha hb
    | true =>
      simp only [d13100, d162573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33202 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d162092 q = 1) : d162574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d162574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d162092 q = 1) : d162575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d162575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d162092 q = 1) : d162576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d162576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d162092 q = 1) : d162579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33203 q ha hb
    | true =>
      simp only [d13106, d162579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33204 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d162092 q = 1) : d162580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d162580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d162092 q = 1) : d162581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d162581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d162092 q = 1) : d162584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33205 q ha hb
    | true =>
      simp only [d13111, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33206 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d162092 q = 1) : d162585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d162092 q = 1) : d162587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33207 q ha hb
    | true =>
      simp only [d13117, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d162092 q = 1) : d162588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d162092 q = 1) : d162589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d162092 q = 1) : d162590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d162590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d162092 q = 1) : d162591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d162591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d162092 q = 1) : d162592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d162592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro33209 (p : Pattern) (ha : d115412 p = 1) (hb : d162092 p = 1) : d162617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d162092 q = 1) : d162584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33205 q ha hb
    | true =>
      simp only [d13111, d162584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33206 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d162092 q = 1) : d162585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d162585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d162092 q = 1) : d162587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33207 q ha hb
    | true =>
      simp only [d13117, d162587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d162092 q = 1) : d162588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d162588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d162092 q = 1) : d162589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d162589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d162092 q = 1) : d162615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d162615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d162092 q = 1) : d162616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d162616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d162092 q = 1) : d162617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d162617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33210 (p : Pattern) (ha : d13155 p = 1) (hb : d162092 p = 1) : d162626 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1379 q = 1) : d1379 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h3 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1384 q = 1) (hb : d162091 q = 1) : d162625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d162091, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1384, d162091, d162625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13155 q = 1) (hb : d162092 q = 1) : d162626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d162092, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13155, d162092, d162626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33211 (p : Pattern) (ha : d13156 p = 1) (hb : d162092 p = 1) : d162628 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1383 q = 1) : d1383 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h3 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1389 q = 1) (hb : d162091 q = 1) : d162627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d162091, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1389, d162091, d162627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13156 q = 1) (hb : d162092 q = 1) : d162628 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d162092, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13156, d162092, d162628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33212 (p : Pattern) (ha : d13179 p = 1) (hb : d162092 p = 1) : d162646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d162092 q = 1) : d162629 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33210 q ha hb
    | true =>
      simp only [d13157, d162629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33211 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d162092 q = 1) : d162630 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d162630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d162092 q = 1) : d162631 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d162631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13169 q = 1) (hb : d162092 q = 1) : d13169 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13170 q = 1) (hb : d162092 q = 1) : d162632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33211 q ha hb
    | true =>
      simp only [d13170, d162632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13171 q = 1) (hb : d162092 q = 1) : d162633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d162633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13172 q = 1) (hb : d162092 q = 1) : d162634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d162634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13173 q = 1) (hb : d162092 q = 1) : d162635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13173, d162635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13174 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33211 q ha hb
    | true =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
  have h10 (q : Pattern) (ha : d13175 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13176 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d6355 q = 1) (hb : d162092 q = 1) : d6355 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d6356 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
    | true =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6357 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d6358 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13177 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13178 q = 1) (hb : d162092 q = 1) : d162645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13178, d162645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13179 q = 1) (hb : d162092 q = 1) : d162646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13179, d162646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro33213 (p : Pattern) (ha : d13183 p = 1) (hb : d162092 p = 1) : d162651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33211 q ha hb
    | true =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6355 q = 1) (hb : d162092 q = 1) : d6355 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6356 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
    | true =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6357 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6358 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13177 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6359 q = 1) (hb : d162092 q = 1) : d162649 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6359, d162649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13182 q = 1) (hb : d162092 q = 1) : d162650 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13182, d162650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13183 q = 1) (hb : d162092 q = 1) : d162651 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13183, d162651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro33214 (p : Pattern) (ha : d13189 p = 1) (hb : d162092 p = 1) : d162657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d162092 q = 1) : d162647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33212 q ha hb
    | true =>
      simp only [d13180, d162647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d162092 q = 1) : d162648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d162648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d162092 q = 1) : d162652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33213 q ha hb
    | true =>
      simp only [d13184, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d162092 q = 1) : d162653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d162092 q = 1) : d162654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d162654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d162092 q = 1) : d162655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d162655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d162092 q = 1) : d162656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d162656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d162092 q = 1) : d162657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d162657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33215 (p : Pattern) (ha : d13202 p = 1) (hb : d162092 p = 1) : d162669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d162092 q = 1) : d162652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33213 q ha hb
    | true =>
      simp only [d13184, d162652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d162092 q = 1) : d162653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d162653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33189 q ha hb
    | true =>
      simp only [d13197, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d162092 q = 1) : d162666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d162666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d162092 q = 1) : d162667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d162667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d162092 q = 1) : d162668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d162668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d162092 q = 1) : d162669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d162669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33216 (p : Pattern) (ha : d13243 p = 1) (hb : d162092 p = 1) : d162673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33211 q ha hb
    | true =>
      simp only [d13174, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6355 q = 1) (hb : d162092 q = 1) : d6355 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6356 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
    | true =>
      simp only [d6356, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6357 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6358 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13177 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d162092 q = 1) : d13190 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13191 q = 1) (hb : d162092 q = 1) : d162658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33188 q ha hb
    | true =>
      simp only [d13191, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13192 q = 1) (hb : d162092 q = 1) : d162659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13193 q = 1) (hb : d162092 q = 1) : d162660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13194 q = 1) (hb : d162092 q = 1) : d162661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13194, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13242 q = 1) (hb : d162092 q = 1) : d162672 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13242, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13243 q = 1) (hb : d162092 q = 1) : d162673 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13243, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro33217 (p : Pattern) (ha : d13249 p = 1) (hb : d162092 p = 1) : d162679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d162092 q = 1) : d162674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33216 q ha hb
    | true =>
      simp only [d13244, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d162092 q = 1) : d162675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d162092 q = 1) : d162676 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d162676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d162092 q = 1) : d162677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d162677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d162092 q = 1) : d162678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d162678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d162092 q = 1) : d162679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d162679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33218 (p : Pattern) (ha : d115422 p = 1) (hb : d162092 p = 1) : d162685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d162092 q = 1) : d162670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33214 q ha hb
    | true =>
      simp only [d13203, d162670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33215 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d162092 q = 1) : d162671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d162671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d162092 q = 1) : d162680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33217 q ha hb
    | true =>
      simp only [d13250, d162680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d162092 q = 1) : d162681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d162681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d162092 q = 1) : d162682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d162682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d162092 q = 1) : d162683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d162683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d162092 q = 1) : d162684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d162684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d162092 q = 1) : d162685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d162685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33219 (p : Pattern) (ha : d115428 p = 1) (hb : d162092 p = 1) : d162702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d162092 q = 1) : d162503 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d162503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33179 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d162092 q = 1) : d162504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d162504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d162092 q = 1) : d162513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33179 q ha hb
    | true =>
      simp only [d12998, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33182 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d162092 q = 1) : d162514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d162092 q = 1) : d162515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d162515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d162092 q = 1) : d162593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33200 q ha hb
    | true =>
      simp only [d115406, d162593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33208 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d162092 q = 1) : d162611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33185 q ha hb
    | true =>
      simp only [d13141, d162611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33186 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d162092 q = 1) : d162612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d162612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d162092 q = 1) : d162613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d162613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d162092 q = 1) : d162614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d162614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d162092 q = 1) : d162618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d162618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33209 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d162092 q = 1) : d162620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d162620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33187 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d162092 q = 1) : d162621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d162621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d162092 q = 1) : d162622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d162622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d162092 q = 1) : d162623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d162623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d162092 q = 1) : d162624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d162624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d162092 q = 1) : d162686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d162686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33218 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d162092 q = 1) : d162697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d162697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33191 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d162092 q = 1) : d162698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d162698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d162092 q = 1) : d162699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d162699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d162092 q = 1) : d162700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d162700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d162092 q = 1) : d162701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d162701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d162092 q = 1) : d162702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d162702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro33220 (p : Pattern) (ha : d115434 p = 1) (hb : d162092 p = 1) : d162708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d162092 q = 1) : d162703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d162703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33219 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d162092 q = 1) : d162704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d162704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d162092 q = 1) : d162705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d162705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d162092 q = 1) : d162706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d162706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d162092 q = 1) : d162707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d162707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d162092 q = 1) : d162708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d162708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33221 (p : Pattern) (ha : d5120 p = 1) (hb : d162092 p = 1) : d162715 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1573 q = 1) : d1573 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1586 q = 1) (hb : d162091 q = 1) : d162714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d162091, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1586, d162091, d162714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5120 q = 1) (hb : d162092 q = 1) : d162715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d162092, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5120, d162092, d162715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33222 (p : Pattern) (ha : d13282 p = 1) (hb : d162092 p = 1) : d162713 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1558 q = 1) : d1558 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1574 q = 1) (hb : d162091 q = 1) : d162712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d162091, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1574, d162091, d162712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13282 q = 1) (hb : d162092 q = 1) : d162713 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d162092, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13282, d162092, d162713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33223 (p : Pattern) (ha : d13293 p = 1) (hb : d162092 p = 1) : d162728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33222 q ha hb
    | true =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5139 q = 1) (hb : d162092 q = 1) : d5139 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5140 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
    | true =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5141 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5142 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13286 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13287 q = 1) (hb : d162092 q = 1) : d13287 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13288 q = 1) (hb : d162092 q = 1) : d162723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
    | true =>
      simp only [d13288, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13289 q = 1) (hb : d162092 q = 1) : d162724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13290 q = 1) (hb : d162092 q = 1) : d162725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13291 q = 1) (hb : d162092 q = 1) : d162726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13291, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13292 q = 1) (hb : d162092 q = 1) : d162727 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13292, d162727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13293 q = 1) (hb : d162092 q = 1) : d162728 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13293, d162728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro33224 (p : Pattern) (ha : d13297 p = 1) (hb : d162092 p = 1) : d162732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13287 q = 1) (hb : d162092 q = 1) : d13287 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13288 q = 1) (hb : d162092 q = 1) : d162723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
    | true =>
      simp only [d13288, d162723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13289 q = 1) (hb : d162092 q = 1) : d162724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d162724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13290 q = 1) (hb : d162092 q = 1) : d162725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d162725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13291 q = 1) (hb : d162092 q = 1) : d162726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13291, d162726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13296 q = 1) (hb : d162092 q = 1) : d162731 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13296, d162731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13297 q = 1) (hb : d162092 q = 1) : d162732 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13297, d162732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33225 (p : Pattern) (ha : d13303 p = 1) (hb : d162092 p = 1) : d162738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d162092 q = 1) : d162737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d162092 q = 1) : d162738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d162738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33226 (p : Pattern) (ha : d13307 p = 1) (hb : d162092 p = 1) : d162742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d162092 q = 1) : d162741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d162092 q = 1) : d162742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d162742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33227 (p : Pattern) (ha : d13313 p = 1) (hb : d162092 p = 1) : d162748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d162092 q = 1) : d162743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33225 q ha hb
    | true =>
      simp only [d13308, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33226 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d162092 q = 1) : d162744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d162092 q = 1) : d162745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d162092 q = 1) : d162746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d162092 q = 1) : d162747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d162092 q = 1) : d162748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33228 (p : Pattern) (ha : d13316 p = 1) (hb : d162092 p = 1) : d162751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d162092 q = 1) : d162737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d162737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d162092 q = 1) : d162751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d162751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro33229 (p : Pattern) (ha : d13317 p = 1) (hb : d162092 p = 1) : d162752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d162092 q = 1) : d162741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d162741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d162092 q = 1) : d162752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d162752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33230 (p : Pattern) (ha : d13323 p = 1) (hb : d162092 p = 1) : d162758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d162092 q = 1) : d162743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33225 q ha hb
    | true =>
      simp only [d13308, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33226 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d162092 q = 1) : d162744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d162092 q = 1) : d162745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d162092 q = 1) : d162746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d162092 q = 1) : d162747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d162092 q = 1) : d162753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33228 q ha hb
    | true =>
      simp only [d13318, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33229 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d162092 q = 1) : d162754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d162092 q = 1) : d162755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d162092 q = 1) : d162756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d162092 q = 1) : d162757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d162092 q = 1) : d162758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33231 (p : Pattern) (ha : d13366 p = 1) (hb : d162092 p = 1) : d162793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33222 q ha hb
    | true =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5139 q = 1) (hb : d162092 q = 1) : d5139 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5140 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
    | true =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5141 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5142 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13286 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5143 q = 1) (hb : d162092 q = 1) : d162791 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5143, d162791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13365 q = 1) (hb : d162092 q = 1) : d162792 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13365, d162792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13366 q = 1) (hb : d162092 q = 1) : d162793 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13366, d162793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro33232 (p : Pattern) (ha : d13376 p = 1) (hb : d162092 p = 1) : d162803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33231 q ha hb
    | true =>
      simp only [d13367, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d162092 q = 1) : d162800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d162800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d162092 q = 1) : d162801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d162801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d162092 q = 1) : d162802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d162802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d162092 q = 1) : d162803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d162803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33233 (p : Pattern) (ha : d13460 p = 1) (hb : d162092 p = 1) : d162849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d162092 q = 1) : d162839 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33232 q ha hb
    | true =>
      simp only [d13450, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33226 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d162092 q = 1) : d162840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d162092 q = 1) : d162841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d162092 q = 1) : d162842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d162092 q = 1) : d162843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d162092 q = 1) : d162844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33226 q ha hb
    | true =>
      simp only [d13455, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d162092 q = 1) : d162845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d162092 q = 1) : d162846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d162092 q = 1) : d162847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d162092 q = 1) : d162848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d162092 q = 1) : d162849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33234 (p : Pattern) (ha : d13466 p = 1) (hb : d162092 p = 1) : d162855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d162092 q = 1) : d162844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33226 q ha hb
    | true =>
      simp only [d13455, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d162092 q = 1) : d162845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d162092 q = 1) : d162846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d162092 q = 1) : d162847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d162092 q = 1) : d162848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d162092 q = 1) : d162850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33229 q ha hb
    | true =>
      simp only [d13461, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d162092 q = 1) : d162851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d162092 q = 1) : d162852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d162092 q = 1) : d162853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d162092 q = 1) : d162854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d162092 q = 1) : d162855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro33235 (p : Pattern) (ha : d13475 p = 1) (hb : d162092 p = 1) : d162864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d162092 q = 1) : d162850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33229 q ha hb
    | true =>
      simp only [d13461, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d162092 q = 1) : d162851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d162092 q = 1) : d162852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d162092 q = 1) : d162853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d162092 q = 1) : d162854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d162092 q = 1) : d162864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33236 (p : Pattern) (ha : d6495 p = 1) (hb : d162092 p = 1) : d162881 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1865 q = 1) : d1865 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1872 q = 1) (hb : d162091 q = 1) : d162880 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d162091, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1872, d162091, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d6495 q = 1) (hb : d162092 q = 1) : d162881 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d162092, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6495, d162092, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro33237 (p : Pattern) (ha : d13522 p = 1) (hb : d162092 p = 1) : d162907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13516 q = 1) (hb : d162092 q = 1) : d13516 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13517 q = 1) (hb : d162092 q = 1) : d162902 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33236 q ha hb
    | true =>
      simp only [d13517, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13518 q = 1) (hb : d162092 q = 1) : d162903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13519 q = 1) (hb : d162092 q = 1) : d162904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13520 q = 1) (hb : d162092 q = 1) : d162905 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13520, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13521 q = 1) (hb : d162092 q = 1) : d162906 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13521, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13522 q = 1) (hb : d162092 q = 1) : d162907 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13522, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro33238 (p : Pattern) (ha : d13586 p = 1) (hb : d162092 p = 1) : d162934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d162092 q = 1) : d162908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33237 q ha hb
    | true =>
      simp only [d13523, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d162092 q = 1) : d162909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d162092 q = 1) : d162931 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d162092 q = 1) : d162932 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d162092 q = 1) : d162933 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d162092 q = 1) : d162934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro33239 (p : Pattern) (ha : d13592 p = 1) (hb : d162092 p = 1) : d162940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d162092 q = 1) : d162935 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33238 q ha hb
    | true =>
      simp only [d13587, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d162092 q = 1) : d162936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d162092 q = 1) : d162937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d162092 q = 1) : d162938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d162092 q = 1) : d162939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d162092 q = 1) : d162940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33240 (p : Pattern) (ha : d13328 p = 1) (hb : d162092 p = 1) : d162763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d162092 q = 1) : d162762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d162092 q = 1) : d162763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d162763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33241 (p : Pattern) (ha : d13330 p = 1) (hb : d162092 p = 1) : d162765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d162092 q = 1) : d162740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d162740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d162092 q = 1) : d162764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d162764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d162092 q = 1) : d162765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d162765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33242 (p : Pattern) (ha : d13337 p = 1) (hb : d162092 p = 1) : d162772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d162092 q = 1) : d162770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d162770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d162092 q = 1) : d162771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d162771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d162092 q = 1) : d162772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d162772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33243 (p : Pattern) (ha : d13340 p = 1) (hb : d162092 p = 1) : d162775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d162092 q = 1) : d162739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d162739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d162092 q = 1) : d162773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d162773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d162092 q = 1) : d162774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d162774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d162092 q = 1) : d162775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d162775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33244 (p : Pattern) (ha : d13344 p = 1) (hb : d162092 p = 1) : d162779 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1668 q = 1) : d1668 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1669 q = 1) (hb : d162091 q = 1) : d16861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d162091, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1669, d162091, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13344 q = 1) (hb : d162092 q = 1) : d162779 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d162092, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13344, d162092, d162779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33245 (p : Pattern) (ha : d13362 p = 1) (hb : d162092 p = 1) : d162788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d162092 q = 1) : d162780 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33244 q ha hb
    | true =>
      simp only [d13345, d162780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33222 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d162092 q = 1) : d162781 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d162781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d162092 q = 1) : d162782 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d162782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13356 q = 1) (hb : d162092 q = 1) : d13356 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13357 q = 1) (hb : d162092 q = 1) : d162783 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33222 q ha hb
    | true =>
      simp only [d13357, d162783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13358 q = 1) (hb : d162092 q = 1) : d162784 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d162784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13359 q = 1) (hb : d162092 q = 1) : d162785 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d162785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13360 q = 1) (hb : d162092 q = 1) : d162786 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13360, d162786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13283 q = 1) (hb : d162092 q = 1) : d162716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33222 q ha hb
    | true =>
      simp only [d13283, d162716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
  have h10 (q : Pattern) (ha : d13284 q = 1) (hb : d162092 q = 1) : d162717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d162717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13285 q = 1) (hb : d162092 q = 1) : d162718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d162718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5139 q = 1) (hb : d162092 q = 1) : d5139 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5140 q = 1) (hb : d162092 q = 1) : d162719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33221 q ha hb
    | true =>
      simp only [d5140, d162719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5141 q = 1) (hb : d162092 q = 1) : d162720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d162720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d5142 q = 1) (hb : d162092 q = 1) : d162721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d162721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13286 q = 1) (hb : d162092 q = 1) : d162722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13286, d162722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13361 q = 1) (hb : d162092 q = 1) : d162787 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13361, d162787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d13362 q = 1) (hb : d162092 q = 1) : d162788 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d13362, d162788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro33246 (p : Pattern) (ha : d13372 p = 1) (hb : d162092 p = 1) : d162799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d162092 q = 1) : d162789 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33245 q ha hb
    | true =>
      simp only [d13363, d162789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d162092 q = 1) : d162790 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d162790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d162092 q = 1) : d162794 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33231 q ha hb
    | true =>
      simp only [d13367, d162794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d162092 q = 1) : d162795 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d162795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d162092 q = 1) : d162796 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d162796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d162092 q = 1) : d162797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d162797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d162092 q = 1) : d162798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d162798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d162092 q = 1) : d162799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d162799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro33247 (p : Pattern) (ha : d13417 p = 1) (hb : d162092 p = 1) : d162809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d162092 q = 1) : d162806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d162092 q = 1) : d162807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d162092 q = 1) : d162808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d162092 q = 1) : d162809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d162809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro33248 (p : Pattern) (ha : d115442 p = 1) (hb : d162092 p = 1) : d162815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d162092 q = 1) : d162766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33240 q ha hb
    | true =>
      simp only [d13331, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33241 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d162092 q = 1) : d162767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d162092 q = 1) : d162768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d162092 q = 1) : d162769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d162092 q = 1) : d162776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33242 q ha hb
    | true =>
      simp only [d13341, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33243 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d162092 q = 1) : d162777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d162092 q = 1) : d162778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d162092 q = 1) : d162804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33246 q ha hb
    | true =>
      simp only [d13377, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33232 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d162092 q = 1) : d162805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d162092 q = 1) : d162810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33247 q ha hb
    | true =>
      simp only [d13418, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d162092 q = 1) : d162811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d162092 q = 1) : d162812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d162092 q = 1) : d162813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d162092 q = 1) : d162814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d162092 q = 1) : d162815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d162815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro33249 (p : Pattern) (ha : d13424 p = 1) (hb : d162092 p = 1) : d162816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d162092 q = 1) : d162729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33223 q ha hb
    | true =>
      simp only [d13294, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d162092 q = 1) : d162730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d162092 q = 1) : d162733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33224 q ha hb
    | true =>
      simp only [d13298, d162733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d162092 q = 1) : d162734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d162734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d162092 q = 1) : d162735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d162735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d162092 q = 1) : d162736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d162736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d162092 q = 1) : d162762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d162762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d162092 q = 1) : d162816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d162816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
